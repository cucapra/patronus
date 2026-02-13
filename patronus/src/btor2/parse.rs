// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::expr::*;
use crate::system::transform::do_transform;
use crate::system::*;
use baa::{BitVecValue, WidthInt};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use std::borrow::Cow;

pub fn parse_str(ctx: &mut Context, input: &str, name: Option<&str>) -> Option<TransitionSystem> {
    match Parser::new(ctx).parse(input.as_bytes(), name) {
        Ok(sys) => Some(sys),
        Err(errors) => {
            report_errors(errors, "str", input);
            None
        }
    }
}

pub fn parse_file<P: AsRef<std::path::Path>>(filename: P) -> Option<(Context, TransitionSystem)> {
    let mut ctx = Context::default();
    let sys = parse_file_with_ctx(filename, &mut ctx)?;
    Some((ctx, sys))
}

pub fn parse_file_with_ctx<P: AsRef<std::path::Path>>(
    filename: P,
    ctx: &mut Context,
) -> Option<TransitionSystem> {
    let path = filename.as_ref();
    let f = std::fs::File::open(path).expect("Failed to open btor file!");
    let reader = std::io::BufReader::new(f);
    let backup_name = path.file_stem().and_then(|n| n.to_str());
    match Parser::new(ctx).parse(reader, backup_name) {
        Ok(sys) => Some(sys),
        Err(errors) => {
            report_errors(
                errors,
                path.file_name().unwrap().to_str().unwrap(),
                &std::fs::read_to_string(path).unwrap(),
            );
            None
        }
    }
}

struct Parser<'a> {
    ctx: &'a mut Context,
    sys: TransitionSystem,
    errors: Errors,
    /// offset of the current line inside the file
    offset: usize,
    /// maps file id to type
    type_map: FxHashMap<LineId, Type>,
    /// maps file id to state in the Transition System
    state_map: FxHashMap<LineId, StateRef>,
    /// maps file id to signal in the Transition System
    signal_map: FxHashMap<LineId, ExprRef>,
    /// keeps track of names in order to uniquify them
    unique_names: FxHashSet<String>,
}

type LineId = u32;

pub const DEFAULT_INPUT_PREFIX: &str = "_input";
pub const DEFAULT_STATE_PREFIX: &str = "_state";
pub const DEFAULT_OUTPUT_PREFIX: &str = "_output";
pub const DEFAULT_BAD_STATE_PREFIX: &str = "_bad";
pub const DEFAULT_CONSTRAINT_PREFIX: &str = "_constraint";

impl<'a> Parser<'a> {
    fn new(ctx: &'a mut Context) -> Self {
        Parser {
            ctx,
            sys: TransitionSystem::new("".to_string()),
            errors: Errors::new(),
            offset: 0,
            type_map: FxHashMap::default(),
            state_map: FxHashMap::default(),
            signal_map: FxHashMap::default(),
            unique_names: FxHashSet::default(),
        }
    }

    fn parse(
        &mut self,
        input: impl std::io::BufRead,
        backup_name: Option<&str>,
    ) -> Result<TransitionSystem, Errors> {
        // ensure that default input and state names are reserved in order to get nicer names
        self.unique_names = FxHashSet::from_iter(
            [
                DEFAULT_CONSTRAINT_PREFIX,
                DEFAULT_OUTPUT_PREFIX,
                DEFAULT_BAD_STATE_PREFIX,
                DEFAULT_INPUT_PREFIX,
                DEFAULT_STATE_PREFIX,
            ]
            .into_iter()
            .map(|s| s.to_string()),
        );

        for line_res in input.lines() {
            let line = line_res.expect("failed to read line");
            let _ignore_errors = self.parse_line(&line);
            self.offset += line.len() + 1; // TODO: this assumes that the line terminates with a single character
        }

        // get a better name if none could be determined from the file content
        // this better name is often derived from the filename or other meta info
        if self.sys.name.is_empty()
            && let Some(name) = backup_name
        {
            self.sys.name = name.to_string();
        }

        // possibly improve state names through yosys aliases which look like:
        // better_name = zext(__state__, 0)
        improve_state_names(self.ctx, &mut self.sys);

        // demote states without next or init to input
        for state in self.sys.states.iter() {
            if state.init.is_none() && state.next.is_none() {
                self.sys.inputs.push(state.symbol);
            }
        }
        self.sys
            .states
            .retain(|s| s.next.is_some() || s.init.is_some());

        // check to see if we encountered any errors
        if self.errors.is_empty() {
            Ok(std::mem::replace(
                &mut self.sys,
                TransitionSystem::new("".to_string()),
            ))
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    fn parse_line(&mut self, line: &str) -> ParseLineResult {
        let cont = tokenize_line(line);
        let tokens = &cont.tokens;
        // TODO: deal with comments
        if tokens.is_empty() {
            // early exit if there are no tokens on this line
            return Ok(());
        }

        // the first token should be an ID
        let line_id = self.parse_line_id(line, tokens[0])?;

        // make sure that there is a second token following the id
        let op: &str = match tokens.get(1) {
            None => {
                return self.add_error(line, tokens[0], "No operation after ID.".to_owned());
            }
            Some(op) => op,
        };

        // check op
        let expr = if UNARY_OPS_SET.contains(op) {
            Some(self.parse_unary_op(line, tokens)?)
        } else if BINARY_OPS_SET.contains(op) {
            Some(self.parse_bin_op(line, tokens)?)
        } else {
            self.require_at_least_n_tokens(line, tokens, 3)?;
            match op {
                "ite" | "write" => {
                    // ternary ops
                    Some(self.parse_ternary_op(line, tokens)?)
                }
                "sort" => {
                    self.parse_sort(line, tokens, line_id)?;
                    None
                }
                "const" | "constd" | "consth" | "zero" | "one" => {
                    Some(self.parse_format(line, tokens, op)?)
                }
                "ones" => Some(self.parse_ones(line, tokens)?),
                "state" => {
                    self.parse_state(line, &cont, line_id)?;
                    None // states are already added, no need to re-add them
                }
                "input" => {
                    self.parse_input(line, &cont, line_id)?;
                    None // inputs are already added, no need to re-add them
                }
                "init" | "next" => {
                    self.parse_state_init_or_next(line, &cont, op == "init")?;
                    None
                }
                "output" | "bad" | "constraint" | "fair" => {
                    let expr = self.get_expr_from_line_id(line, tokens[2])?;
                    let name = match op {
                        "output" => {
                            let name = self.get_label_name(&cont, DEFAULT_OUTPUT_PREFIX);
                            self.sys.outputs.push(Output { name, expr });
                            name
                        }
                        "bad" => {
                            self.sys.bad_states.push(expr);
                            self.get_label_name(&cont, DEFAULT_BAD_STATE_PREFIX)
                        }
                        "constraint" => {
                            self.sys.constraints.push(expr);
                            self.get_label_name(&cont, DEFAULT_CONSTRAINT_PREFIX)
                        }
                        "fair" => todo!("support fairness constraints"),
                        _ => unreachable!(),
                    };

                    // we add the name here directly to avoid calling add_unique_str twice
                    self.sys.names[expr] = Some(name);

                    None
                }
                other => {
                    if OTHER_OPS_SET.contains(other) {
                        panic!("TODO: implement support for {other} operation")
                    } else {
                        return self.invalid_op_error(line, op);
                    }
                }
            }
        };
        if let Some((e, token_count)) = expr {
            self.signal_map.insert(line_id, e);
            // try to find a name
            let name = match cont.tokens.get(token_count) {
                None => None,
                Some(name) => {
                    if include_name(name) {
                        Some(self.add_unique_str(&clean_up_name(name)))
                    } else {
                        None
                    }
                }
            };
            // add name if available
            if let Some(name) = name {
                self.sys.names[e] = Some(name);
            }
        }
        Ok(())
    }

    fn add_unique_str(&mut self, start: &str) -> StringRef {
        let mut count: usize = 0;
        let mut name = start.to_string();
        while self.unique_names.contains(&name) {
            name = format!("{start}_{count}");
            count += 1;
        }
        let id = self.ctx.string(Cow::Borrowed(&name));
        self.unique_names.insert(name);
        id
    }

    fn check_expr_type(
        &mut self,
        expr: ExprRef,
        line: &str,
        expected_type: Type,
    ) -> ParseLineResult<ExprRef> {
        // first we check for internal consistency
        if let Err(e) = expr.type_check(self.ctx) {
            let _ = self.add_error(line, line, format!("Failed to type check: {}", e.get_msg()));
            return Err(());
        }
        // then we make sure that the type of the expression is actually the type that was
        // declared in the btor2 line
        let actual_tpe = expr.get_type(self.ctx);
        if actual_tpe != expected_type {
            let _ =
                self.add_error(line, line, format!("Expression has the type {actual_tpe}, but the declared btpr2 type is {expected_type}", ));
            Err(())
        } else {
            Ok(expr)
        }
    }

    fn check_type(
        &mut self,
        actual: &Type,
        expected: &Type,
        line: &str,
        token: &str,
        msg: &str,
    ) -> ParseLineResult {
        if actual == expected {
            Ok(())
        } else {
            self.add_error(line, token, format!("{msg}: {actual} != {expected}"))
        }
    }

    fn get_label_name(&mut self, cont: &LineTokens, default: &str) -> StringRef {
        // look at last token and see if it is not a

        let base_str: &str = cont.tokens.get(3).unwrap_or(&default);
        // TODO: look into comment for better names
        self.add_unique_str(base_str)
    }

    fn parse_unary_op(&mut self, line: &str, tokens: &[&str]) -> ParseLineResult<(ExprRef, usize)> {
        self.require_at_least_n_tokens(line, tokens, 4)?;
        let tpe = self.get_tpe_from_id(line, tokens[2])?;
        let e = self.get_expr_from_line_id(line, tokens[3])?;
        let (res, token_count) = match tokens[1] {
            "slice" => {
                // slice has two integer attributes
                self.require_at_least_n_tokens(line, tokens, 6)?;
                let msb = self.parse_width_int(line, tokens[4], "slice msb")?;
                let lsb = self.parse_width_int(line, tokens[5], "slice lsb")?;
                (self.ctx.slice(e, msb, lsb), 6)
            }
            "not" => (self.ctx.not(e), 4),
            "neg" => (self.ctx.negate(e), 4),
            "uext" => {
                self.require_at_least_n_tokens(line, tokens, 5)?;
                let by = self.parse_width_int(line, tokens[4], "extension amount")?;
                (self.ctx.zero_extend(e, by), 5)
            }
            "sext" => {
                self.require_at_least_n_tokens(line, tokens, 5)?;
                let by = self.parse_width_int(line, tokens[4], "extension amount")?;
                (self.ctx.sign_extend(e, by), 5)
            }
            "redor" => {
                let width = e.get_type(self.ctx).get_bit_vector_width().unwrap();
                if width == 1 {
                    (e, 4)
                } else {
                    // redor is true iff at least one bit is a one
                    let zero = self.ctx.zero(width);
                    let eq_zero = self.ctx.equal(e, zero);
                    (self.ctx.not(eq_zero), 4)
                }
            }
            "redand" => {
                let width = e.get_type(self.ctx).get_bit_vector_width().unwrap();
                if width == 1 {
                    (e, 4)
                } else {
                    // redand is true iff all bits are one
                    let mask = self.ctx.ones(width);
                    (self.ctx.equal(e, mask), 4)
                }
            }
            "redxor" => {
                let width = e.get_type(self.ctx).get_bit_vector_width().unwrap();
                if width == 1 {
                    (e, 4)
                } else {
                    let bits: Vec<_> = (0..width).map(|ii| self.ctx.slice(e, ii, ii)).collect();
                    let res = bits
                        .into_iter()
                        .reduce(|acc, e| self.ctx.xor(acc, e))
                        .unwrap();
                    (res, 4)
                }
            }
            other => panic!("unexpected unary op: {other}"),
        };
        let checked = self.check_expr_type(res, line, tpe)?;
        Ok((checked, token_count))
    }

    fn parse_bin_op(&mut self, line: &str, tokens: &[&str]) -> ParseLineResult<(ExprRef, usize)> {
        self.require_at_least_n_tokens(line, tokens, 5)?;
        let tpe = self.get_tpe_from_id(line, tokens[2])?;
        let a = self.get_expr_from_line_id(line, tokens[3])?;
        let b = self.get_expr_from_line_id(line, tokens[4])?;
        let e: ExprRef = match tokens[1] {
            "iff" => {
                self.check_type(
                    &tpe,
                    &Type::BOOL,
                    line,
                    tokens[2],
                    "iff always returns bool",
                )?;
                self.check_type(
                    &a.get_type(self.ctx),
                    &Type::BOOL,
                    line,
                    tokens[3],
                    "iff expects a boolean argument",
                )?;
                self.check_type(
                    &b.get_type(self.ctx),
                    &Type::BOOL,
                    line,
                    tokens[4],
                    "iff expects a boolean argument",
                )?;
                self.ctx.equal(a, b)
            }
            "implies" => self.ctx.implies(a, b),
            "sgt" => self.ctx.greater_signed(a, b),
            "ugt" => self.ctx.greater(a, b),
            "sgte" => self.ctx.greater_or_equal_signed(a, b),
            "ugte" => self.ctx.greater_or_equal(a, b),
            "slt" => self.ctx.greater_signed(b, a),
            "ult" => self.ctx.greater(b, a),
            "slte" => self.ctx.greater_or_equal_signed(b, a),
            "ulte" => self.ctx.greater_or_equal(b, a),
            "and" => self.ctx.and(a, b),
            "nand" => {
                let inner = self.ctx.and(a, b);
                self.check_expr_type(inner, line, tpe)?;
                self.ctx.not(inner)
            }
            "nor" => {
                let inner = self.ctx.or(a, b);
                self.check_expr_type(inner, line, tpe)?;
                self.ctx.not(inner)
            }
            "or" => self.ctx.or(a, b),
            "xnor" => {
                let inner = self.ctx.xor(a, b);
                self.check_expr_type(inner, line, tpe)?;
                self.ctx.not(inner)
            }
            "xor" => self.ctx.xor(a, b),
            "rol" | "ror" => todo!("Add support for bit rotates."),
            "sll" => self.ctx.shift_left(a, b),
            "sra" => self.ctx.arithmetic_shift_right(a, b),
            "srl" => self.ctx.shift_right(a, b),
            "add" => self.ctx.add(a, b),
            "mul" => self.ctx.mul(a, b),
            "sdiv" => self.ctx.signed_div(a, b),
            "udiv" => self.ctx.div(a, b),
            "smod" => self.ctx.signed_mod(a, b),
            "srem" => self.ctx.signed_remainder(a, b),
            "urem" => self.ctx.remainder(a, b),
            "sub" => self.ctx.sub(a, b),
            "saddo" | "uaddo" | "sdivo" | "udivo" | "smulo" | "umulo" | "ssubo" | "usubo" => {
                todo!("Add support for overflow operators")
            }
            "concat" => self.ctx.concat(a, b),
            "eq" => self.ctx.equal(a, b),
            "neq" => {
                let inner = self.ctx.equal(a, b);
                self.check_expr_type(inner, line, tpe)?;
                self.ctx.not(inner)
            }
            "read" => self.ctx.array_read(a, b),
            other => panic!("unexpected binary op: {other}"),
        };
        let checked = self.check_expr_type(e, line, tpe)?;
        Ok((checked, 5))
    }

    fn parse_ternary_op(
        &mut self,
        line: &str,
        tokens: &[&str],
    ) -> ParseLineResult<(ExprRef, usize)> {
        self.require_at_least_n_tokens(line, tokens, 6)?;
        let tpe = self.get_tpe_from_id(line, tokens[2])?;
        let a = self.get_expr_from_line_id(line, tokens[3])?;
        let b = self.get_expr_from_line_id(line, tokens[4])?;
        let c = self.get_expr_from_line_id(line, tokens[5])?;
        let res: ExprRef = match tokens[1] {
            "ite" => self.ctx.ite(a, b, c),
            "write" => self.ctx.array_store(a, b, c),
            other => panic!("unexpected binary op: {other}"),
        };
        let checked = self.check_expr_type(res, line, tpe)?;
        Ok((checked, 6))
    }

    fn parse_state(
        &mut self,
        line: &str,
        cont: &LineTokens,
        line_id: LineId,
    ) -> ParseLineResult<()> {
        let tpe = self.get_tpe_from_id(line, cont.tokens[2])?;
        let name = self.get_label_name(cont, DEFAULT_STATE_PREFIX);
        let symbol = self.ctx.symbol(name, tpe);
        let state = State {
            symbol,
            next: None,
            init: None,
        };
        let state_ref = self.sys.add_state(self.ctx, state);
        self.state_map.insert(line_id, state_ref);
        self.signal_map.insert(line_id, symbol);
        Ok(())
    }

    fn parse_input(
        &mut self,
        line: &str,
        cont: &LineTokens,
        line_id: LineId,
    ) -> ParseLineResult<()> {
        let tpe = self.get_tpe_from_id(line, cont.tokens[2])?;
        let name = self.get_label_name(cont, DEFAULT_INPUT_PREFIX);
        let sym = self.ctx.symbol(name, tpe);
        self.sys.add_input(self.ctx, sym);
        self.signal_map.insert(line_id, sym);
        Ok(())
    }

    fn parse_state_init_or_next(
        &mut self,
        line: &str,
        cont: &LineTokens,
        is_init_not_next: bool,
    ) -> ParseLineResult {
        let lbl = if is_init_not_next { "init" } else { "next" };
        self.require_at_least_n_tokens(line, &cont.tokens, 5)?;
        let tpe = self.get_tpe_from_id(line, cont.tokens[2])?;
        let state_ref = self.get_state_from_id(line, cont.tokens[3])?;
        let state_sym = self.sys.get_state(state_ref).symbol;
        let state_tpe = state_sym.type_check(self.ctx).unwrap();
        let state_name = self.ctx.get_symbol_name(state_sym).unwrap().to_string();
        self.check_type(
            &state_tpe,
            &tpe,
            line,
            cont.tokens[4],
            &format!("[{state_name}.{lbl}] Expression type does not match state type."),
        )?;

        let maybe_expr = self.get_expr_from_line_id(line, cont.tokens[4])?;
        // for state init, sometimes array states are assigned a bv-type expression
        let bv_assigned_to_array =
            maybe_expr.get_type(self.ctx).is_bit_vector() && state_tpe.is_array();
        let expr = if is_init_not_next && bv_assigned_to_array {
            self.ctx
                .array_const(maybe_expr, state_tpe.get_array_index_width().unwrap())
        } else {
            maybe_expr
        };
        self.check_type(
            &expr.get_type(self.ctx),
            &tpe,
            line,
            cont.tokens[4],
            &format!("[{state_name}.{lbl}] Expressions has mismatched type"),
        )?;

        if is_init_not_next {
            self.sys
                .modify_state(state_ref, |state| state.init = Some(expr));
        } else {
            self.sys
                .modify_state(state_ref, |state| state.next = Some(expr));
        }
        Ok(())
    }

    fn parse_line_id(&mut self, line: &str, token: &str) -> ParseLineResult<LineId> {
        match token.parse::<LineId>().ok() {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    "Expected valid non-negative integer ID.".to_owned(),
                );
                Err(())
            }
            Some(id) => Ok(id),
        }
    }

    fn parse_ones(&mut self, line: &str, tokens: &[&str]) -> ParseLineResult<(ExprRef, usize)> {
        self.require_at_least_n_tokens(line, tokens, 3)?;
        // derive width from type
        let width = self.get_bv_width(line, tokens[2])?;
        let value = baa::BitVecValue::ones(width);
        Ok((self.ctx.bv_lit(&value), 3))
    }

    fn parse_format(
        &mut self,
        line: &str,
        tokens: &[&str],
        op: &str,
    ) -> ParseLineResult<(ExprRef, usize)> {
        self.require_at_least_n_tokens(line, tokens, 3)?;
        // derive width from type
        let width = self.get_bv_width(line, tokens[2])?;

        let res = match op {
            "zero" => Ok(self.ctx.zero(width)),
            "one" => Ok(self.ctx.one(width)),
            "const" => self.parse_bv_lit_str(line, tokens[3], 2, width),
            "constd" => self.parse_bv_lit_str(line, tokens[3], 10, width),
            "consth" => self.parse_bv_lit_str(line, tokens[3], 16, width),
            other => panic!("Did not expect {other} as a possible format op!"),
        }?;
        let tokens = if op.starts_with("const") { 4 } else { 3 };
        Ok((res, tokens))
    }

    fn parse_bv_lit_str(
        &mut self,
        line: &str,
        token: &str,
        base: u32,
        width: WidthInt,
    ) -> ParseLineResult<ExprRef> {
        match BitVecValue::from_str_radix(token, base, width) {
            Ok(val) => Ok(self.ctx.bv_lit(&val)),
            Err(_) => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("Failed to parse as an integer of base {base}"),
                );
                Err(())
            }
        }
    }

    fn get_bv_width(&mut self, line: &str, token: &str) -> ParseLineResult<WidthInt> {
        let tpe = self.get_tpe_from_id(line, token)?;
        match tpe {
            Type::BV(width) => Ok(width),
            Type::Array(tpe) => {
                let _ = self.add_error(
                    line,
                    token,
                    format!(
                        "Points to an array type `{tpe:?}`, but a bit-vector type is required!"
                    ),
                );
                Err(())
            }
        }
    }

    fn get_tpe_from_id(&mut self, line: &str, token: &str) -> ParseLineResult<Type> {
        let tpe_id = self.parse_line_id(line, token)?;
        match self.type_map.get(&tpe_id) {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("ID `{tpe_id}` does not point to a valid type!"),
                );
                Err(())
            }
            Some(tpe) => Ok(*tpe),
        }
    }

    fn get_state_from_id(&mut self, line: &str, token: &str) -> ParseLineResult<StateRef> {
        let state_id = self.parse_line_id(line, token)?;
        match self.state_map.get(&state_id) {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("ID `{state_id}` does not point to a valid state!"),
                );
                Err(())
            }
            Some(state) => Ok(*state),
        }
    }

    fn get_expr_from_line_id(&mut self, line: &str, token: &str) -> ParseLineResult<ExprRef> {
        let signal_id = self.parse_line_id(line, token)?;
        let expr_ref = match self.signal_map.get(&signal_id) {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("ID `{signal_id}` does not point to a valid signal!"),
                );
                Err(())
            }
            Some(signal) => Ok(*signal),
        }?;
        Ok(expr_ref)
    }

    fn parse_sort(&mut self, line: &str, tokens: &[&str], line_id: LineId) -> ParseLineResult {
        self.require_at_least_n_tokens(line, tokens, 3)?;
        match tokens[2] {
            "bitvec" => {
                self.require_at_least_n_tokens(line, tokens, 4)?;
                let width = self.parse_width_int(line, tokens[3], "bit-vector width")?;
                self.type_map.insert(line_id, Type::BV(width));
                Ok(())
            }
            "array" => {
                self.require_at_least_n_tokens(line, tokens, 5)?;
                let index_tpe = self.get_tpe_from_id(line, tokens[3])?;
                let data_tpe = self.get_tpe_from_id(line, tokens[4])?;
                let index_width = index_tpe.get_bit_vector_width().unwrap();
                let data_width = data_tpe.get_bit_vector_width().unwrap();
                self.type_map.insert(
                    line_id,
                    Type::Array(ArrayType {
                        index_width,
                        data_width,
                    }),
                );
                Ok(())
            }
            other => self.add_error(
                line,
                tokens[2],
                format!("Expected `bitvec` or `array`. Not `{other}`."),
            ),
        }
    }

    fn parse_width_int(
        &mut self,
        line: &str,
        token: &str,
        kind: &str,
    ) -> ParseLineResult<WidthInt> {
        match token.parse::<WidthInt>() {
            Ok(width) => Ok(width),
            Err(_) => {
                let _ = self.add_error(
                    line,
                    token,
                    format!(
                        "Not a valid {kind}. An integer between {} and {} is required!",
                        WidthInt::MAX,
                        WidthInt::MIN
                    ),
                );
                Err(())
            }
        }
    }

    fn add_error(&mut self, line: &str, token: &str, msg: String) -> ParseLineResult {
        let explain = "".to_owned(); // TODO: how do we best utilize both msg and explain?
        let start = str_offset(token, line);
        let end = start + token.len();
        let e = ParserError {
            msg,
            explain,
            start: start + self.offset,
            end: end + self.offset,
        };
        self.errors.push(e);
        Err(())
    }

    fn require_at_least_n_tokens(
        &mut self,
        line: &str,
        tokens: &[&str],
        n: usize,
    ) -> ParseLineResult {
        if tokens.len() < n {
            let op = tokens[1];
            let start = str_offset(op, line);
            let last_token = tokens.last().unwrap();
            let end = str_offset(last_token, line) + last_token.len();
            self.add_error(
                line,
                &line[start..end],
                format!(
                    "{op} requires at least {n} tokens, only {} provided",
                    tokens.len()
                ),
            )
        } else {
            Ok(())
        }
    }

    fn invalid_op_error(&mut self, line: &str, op: &str) -> ParseLineResult {
        let all_ops = UNARY_OPS
            .iter()
            .chain(BINARY_OPS.iter())
            .chain(TERNARY_OPS.iter())
            .chain(OTHER_OPS.iter())
            .cloned()
            .collect::<Vec<_>>();
        self.add_error(
            line,
            op,
            format!(
                "Invalid op {op}. Available ops are: {}?",
                all_ops.join(", ")
            ),
        )
    }
}

/// yosys likes to use a lot of $ in the signal names, we want to avoid that for readability reasons
fn clean_up_name(name: &str) -> String {
    name.replace('$', "_")
}

/// decides whether a name should be included or ignored
fn include_name(name: &str) -> bool {
    // yosys sometime includes complete file paths which are not super helpful
    let yosys_path = name.contains('/') && name.contains(':') && name.len() > 30;
    let yosys_flatten_output = name.starts_with("$flatten\\");
    !yosys_path && !yosys_flatten_output
}

/// When Yosys emits a btor file, it often will not actually name the states correctly.
/// Instead it creates nodes that just point to the state and carry its name. This function searches
/// for these nodes and tries to rename the states.
fn improve_state_names(ctx: &mut Context, sys: &mut TransitionSystem) {
    let mut renames = FxHashMap::default();
    for state in sys.states.iter() {
        // since the alias signal refers to the same expression as the state symbol,
        // it will generate a signal info with the better name
        if let Some(name_ref) = sys.names[state.symbol] {
            let old_name_ref = ctx[state.symbol].get_symbol_name_ref().unwrap();
            if old_name_ref != name_ref {
                renames.insert(state.symbol, name_ref);
            }
        }
    }
    if renames.is_empty() {
        return; // noting to do
    }
    do_transform(
        ctx,
        sys,
        ExprTransformMode::SingleStep,
        |ctx, expr_ref, _| {
            renames
                .get(&expr_ref)
                .map(|new_name_ref| ctx.symbol(*new_name_ref, expr_ref.get_type(ctx)))
        },
    );
}

// Line Tokenizer
#[derive(Default, Debug)]
pub(crate) struct LineTokens<'a> {
    pub(crate) tokens: SmallVec<[&'a str; 4]>,
    pub(crate) comment: Option<&'a str>,
}

const NO_TOKEN: usize = usize::MAX;
pub(crate) fn tokenize_line(line: &str) -> LineTokens<'_> {
    if line.is_empty() {
        // special handling for empty lines
        return LineTokens::default();
    }
    let line_len = line.len();
    let mut out = LineTokens::default();
    let mut token_start: usize = NO_TOKEN;
    #[inline]
    fn finish_token<'a>(
        token_start: &mut usize,
        out: &mut LineTokens<'a>,
        line: &'a str,
        ii: usize,
    ) {
        if *token_start != NO_TOKEN {
            out.tokens.push(&line[*token_start..ii]);
            *token_start = NO_TOKEN;
        }
    }

    for (ii, cc) in line.char_indices() {
        match cc {
            // white space character
            ' ' | '\t' => finish_token(&mut token_start, &mut out, line, ii),
            // comment start
            ';' => {
                finish_token(&mut token_start, &mut out, line, ii);
                out.comment = Some(&line[ii + 1..line_len]);
                return out;
            }
            _ => {
                if token_start == NO_TOKEN {
                    token_start = ii
                }
            }
        }
    }
    finish_token(&mut token_start, &mut out, line, line_len);
    out
}

#[derive(Debug)]
struct ParserError {
    msg: String,
    explain: String, // displayed next to offending token
    start: usize,
    end: usize,
}

type Errors = Vec<ParserError>;

fn report_errors(errors: Errors, name: &str, source: &str) {
    let report_file = codespan_reporting::files::SimpleFile::new(name, source);
    for err in errors.into_iter() {
        report_error(err, &report_file);
    }
}

fn report_error(error: ParserError, file: &codespan_reporting::files::SimpleFile<&str, &str>) {
    let diagnostic = codespan_reporting::diagnostic::Diagnostic::error()
        .with_message(error.msg)
        .with_labels(vec![
            codespan_reporting::diagnostic::Label::primary((), error.start..error.end)
                .with_message(error.explain),
        ]);
    let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        codespan_reporting::term::termcolor::ColorChoice::Auto,
    );
    let config = codespan_reporting::term::Config::default();
    codespan_reporting::term::emit(&mut writer.lock(), &config, file, &diagnostic).unwrap();
}

fn str_offset(needle: &str, haystack: &str) -> usize {
    let offset = (needle.as_ptr() as usize) - (haystack.as_ptr() as usize);
    assert!(
        offset < haystack.len(),
        "{} is not fully contained in {}",
        needle,
        haystack
    );
    offset
}

const UNARY_OPS: [&str; 10] = [
    "not", "inc", "dec", "neg", "redand", "redor", "redxor", "slice", "uext", "sext",
];
const BINARY_OPS: [&str; 41] = [
    "iff", "implies", "sgt", "ugt", "sgte", "ugte", "slt", "ult", "slte", "ulte", "and", "nand",
    "nor", "or", "xnor", "xor", "rol", "ror", "sll", "sra", "srl", "add", "mul", "sdiv", "udiv",
    "smod", "srem", "urem", "sub", "saddo", "uaddo", "sdivo", "udivo", "smulo", "umulo", "ssubo",
    "usubo", "concat", "eq", "neq", "read",
];
const TERNARY_OPS: [&str; 1] = ["ite"];
const OTHER_OPS: [&str; 17] = [
    "sort",
    "input",
    "output",
    "bad",
    "constraint",
    "fair",
    "state",
    "next",
    "init",
    "const",
    "constd",
    "consth",
    "zero",
    "one",
    "ones",
    "read",
    "write",
];

lazy_static! {
    static ref UNARY_OPS_SET: FxHashSet<&'static str> = FxHashSet::from_iter(UNARY_OPS);
    static ref BINARY_OPS_SET: FxHashSet<&'static str> = FxHashSet::from_iter(BINARY_OPS);
    static ref OTHER_OPS_SET: FxHashSet<&'static str> = FxHashSet::from_iter(OTHER_OPS);
}

/// Indicated success or failure. Errors and data is not returned, but rather added to the context.
type ParseLineResult<T = ()> = std::result::Result<T, ()>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize() {
        // correct number of tokens
        assert_eq!(tokenize_line("").tokens.len(), 0);
        assert_eq!(tokenize_line("a").tokens.len(), 1);
        assert_eq!(tokenize_line(" a").tokens.len(), 1);
        assert_eq!(tokenize_line("a ").tokens.len(), 1);
        assert_eq!(tokenize_line(" a ").tokens.len(), 1);
        assert_eq!(tokenize_line("a b").tokens.len(), 2);
        assert_eq!(tokenize_line("a \t b").tokens.len(), 2);
        assert_eq!(tokenize_line("a     b").tokens.len(), 2);
        assert_eq!(tokenize_line("a b ; c").tokens.len(), 2);
        assert_eq!(tokenize_line("a b;c").tokens.len(), 2);
        // correctly deal with whitespace
        assert_eq!(tokenize_line("a").tokens[0], "a");
        assert_eq!(tokenize_line(" a").tokens[0], "a");
        assert_eq!(tokenize_line("a ").tokens[0], "a");
        assert_eq!(tokenize_line(" a ").tokens[0], "a");
        // comments
        let comment_res = tokenize_line("a b; c");
        assert_eq!(comment_res.comment, Some(" c"));
        assert_eq!(comment_res.tokens[0], "a");
        assert_eq!(comment_res.tokens[1], "b");
        // unicode (not sure if this is actually supported by the btor2 format...)
        let unicode_res = tokenize_line("✔ 1✖2  ○;○123");
        assert_eq!(unicode_res.tokens.len(), 3);
        assert!(unicode_res.comment.is_some());
        assert_eq!(unicode_res.tokens[0], "✔");
        assert_eq!(unicode_res.tokens[1], "1✖2");
        assert_eq!(unicode_res.tokens[2], "○");
        assert_eq!(unicode_res.comment.unwrap(), "○123");
    }

    fn parse_private(code: &str) -> Result<TransitionSystem, Errors> {
        let mut ctx = Context::default();
        Parser::new(&mut ctx).parse(code.as_bytes(), None)
    }

    #[test]
    fn parse_failures() {
        parse_private("").expect("parsing an empty line should be fine");
        parse_private("   ").expect("parsing an line with just whitespace should be fine");
        parse_private("  ; test bla  ").expect("parsing an line with a comment should be fine");
        parse_private("not_an_id").expect_err("invalid id");
        parse_private("-1").expect_err("invalid id");
        parse_private("0").expect_err("missing op");
        parse_private("0 ").expect_err("missing op");
    }
}
