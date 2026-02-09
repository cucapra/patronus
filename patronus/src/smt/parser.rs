// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{ArrayType, Context, ExprRef, SerializableIrNode, Type, TypeCheck, WidthInt};
use crate::smt::{Logic, SmtCommand};
use regex::bytes::RegexSet;
use rustc_hash::FxHashMap;
use std::fmt::{Debug, Formatter};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SmtParserError {
    #[error("[smt] {0} requires at least {1} arguments, only {2} found.")]
    MissingArgs(String, u16, u16),
    #[error("[smt] {0} requires at most {1} arguments, but {2} found.")]
    TooManyArgs(String, u16, u16),
    #[error("[smt] expected type, got expression: {0}")]
    ExprInsteadOfType(String),
    #[error("[smt] expected expression, got type: {0}")]
    TypeInsteadOfExpr(String),
    #[error("[smt] invalid key in set-option command: `{0}`")]
    InvalidOptionKey(String),
    #[error("[smt] unknown command: `{0}`")]
    UnknownCommand(String),
    #[error("[smt] unsupported logic: `{0}`")]
    UnknownLogic(String),
    #[error("[smt] only part of the input string was parsed into an expr. Next token: `{0}`")]
    ExprSuffix(String),
    #[error("[smt] expected an opening parenthesis, encountered this instead: {0}")]
    MissingOpen(String),
    #[error("[smt] expected a closing parenthesis, encountered this instead: {0}")]
    MissingClose(String),
    #[error("[smt] get-value response: {0}")]
    GetValueResponse(String),
    #[error("[smt] expected an identifier token but got: {0}")]
    ExpectedIdentifer(String),
    #[error("[smt] expected an expression but got: {0}")]
    ExpectedExpr(String),
    #[error("[smt] expected a type but got: {0}")]
    ExpectedType(String),
    #[error("[smt] expected a command but got: {0}")]
    ExpectedCommand(String),
    #[error("[smt] unknown pattern: {0}")]
    Pattern(String),
    #[error("[smt] missing opening parenthesis for closing parenthesis")]
    ClosingParenWithoutOpening,
    #[error("[smt] unsupported feature {0}")]
    Unsupported(String),
    #[error("[smt] unknown symbol {0}")]
    UnknownSymbol(String),
    #[error("[smt] failed to parse integer {0}")]
    ParseInt(String),
    #[error("[smt] not valid UTF-8 (and thus also not valid ASCII!)")]
    Utf8(#[from] std::str::Utf8Error),
    #[error("[smt] I/O operation failed")]
    Io(#[from] std::io::Error),
}

impl From<baa::ParseIntError> for SmtParserError {
    fn from(value: baa::ParseIntError) -> Self {
        SmtParserError::ParseInt(format!("{value:?}"))
    }
}

impl From<std::num::ParseIntError> for SmtParserError {
    fn from(value: std::num::ParseIntError) -> Self {
        SmtParserError::ParseInt(format!("{value:?}"))
    }
}

type Result<T> = std::result::Result<T, SmtParserError>;

type SymbolTable = FxHashMap<String, ExprRef>;

pub fn parse_expr(ctx: &mut Context, st: &SymbolTable, input: &[u8]) -> Result<ExprRef> {
    let mut lexer = Lexer::new(input);
    let mut nested = NestedSymbolTable::new(st);
    let expr = parse_expr_internal(ctx, &mut nested, &mut lexer)?;
    let token_after_expr = lexer.next_no_comment();
    if token_after_expr.is_some() {
        Err(SmtParserError::ExprSuffix(format!("{token_after_expr:?}")))
    } else {
        Ok(expr)
    }
}

#[derive(Debug)]
struct NestedSymbolTable<'a> {
    /// top-level symbol table, for symbols defined outside the current expression being parsed
    top: &'a SymbolTable,
    /// any symbols defined inside the expression, query this one first
    lets: FxHashMap<String, ExprRef>,
    /// all we need to know in order to be able to undo let bindings correctly
    undo_stack: Vec<LetUndo>,
}

#[derive(Debug)]
enum LetUndo {
    Remove(String),
    Replace(String, ExprRef),
}

impl<'a> NestedSymbolTable<'a> {
    fn new(top: &'a SymbolTable) -> Self {
        Self {
            top,
            lets: Default::default(),
            undo_stack: vec![],
        }
    }

    fn get(&self, name: &str) -> Option<ExprRef> {
        self.lets.get(name).or_else(|| self.top.get(name)).cloned()
    }

    fn push_let(&mut self, name: std::borrow::Cow<str>, expr: ExprRef) {
        // check to see how we will have to modify the lets table to restore it to its previous state
        let undo = match self.lets.get(name.as_ref()) {
            None => LetUndo::Remove(name.to_string()),
            Some(old) => LetUndo::Replace(name.to_string(), *old),
        };
        self.undo_stack.push(undo);

        // modify table
        self.lets.insert(name.into_owned(), expr);
    }

    fn pop_let(&mut self) {
        debug_assert!(!self.lets.is_empty() && !self.undo_stack.is_empty());
        match self.undo_stack.pop().unwrap() {
            LetUndo::Remove(k) => self.lets.remove(&k),
            LetUndo::Replace(k, v) => self.lets.insert(k, v),
        };
    }
}

fn parse_expr_internal(
    ctx: &mut Context,
    st: &mut NestedSymbolTable,
    lexer: &mut Lexer,
) -> Result<ExprRef> {
    match parse_expr_or_type(ctx, st, lexer)? {
        ExprOrType::E(e) => Ok(e),
        ExprOrType::T(t) => Err(SmtParserError::TypeInsteadOfExpr(format!("{t:?}"))),
    }
}

fn parse_type(ctx: &mut Context, st: &mut NestedSymbolTable, lexer: &mut Lexer) -> Result<Type> {
    match parse_expr_or_type(ctx, st, lexer)? {
        ExprOrType::T(t) => Ok(t),
        ExprOrType::E(e) => Err(SmtParserError::ExprInsteadOfType(e.serialize_to_str(ctx))),
    }
}

enum ExprOrType {
    E(ExprRef),
    T(Type),
}

fn parse_expr_or_type(
    ctx: &mut Context,
    st: &mut NestedSymbolTable,
    lexer: &mut Lexer,
) -> Result<ExprOrType> {
    use ParserItem::*;
    let mut stack: Vec<ParserItem> = Vec::with_capacity(64);
    // keep track of how many closing parenthesis without an opening one are encountered
    let mut orphan_closing_count = 0u64;
    for token in lexer {
        match token {
            Token::Open => {
                if orphan_closing_count > 0 {
                    return Err(SmtParserError::ClosingParenWithoutOpening);
                }

                // Open parenthesis tokens get consumed into a Let
                // - "let (" becomes `Let(1)`
                // - "let ((" becomes `Let(2)`
                if let Some(Let(parens)) = stack.last() {
                    debug_assert!(
                        *parens < 2,
                        "We never expect parens to exceed two. But could that happen?"
                    );
                    *stack.last_mut().unwrap() = Let(parens + 1);
                } else {
                    stack.push(Open(false));
                }
            }
            Token::Close => {
                match stack.last() {
                    // `let (( ... )` -> `let (( ... ))`
                    Some(LetScopeOpenMissingClose) => *stack.last_mut().unwrap() = Open(true),
                    _ => {
                        // find the closest Open
                        if let Some(p) = stack.iter().rev().position(|i| matches!(i, Open(_))) {
                            let open_pos = stack.len() - 1 - p;
                            let pattern = &stack[open_pos + 1..];
                            let result = parse_pattern(ctx, st, pattern)?;
                            stack.truncate(open_pos);
                            stack.push(result);
                        } else {
                            // no matching open parenthesis
                            orphan_closing_count += 1;
                        }
                    }
                }
            }
            Token::Value(value) => {
                if orphan_closing_count > 0 {
                    return Err(SmtParserError::ClosingParenWithoutOpening);
                }
                // If this token follows a `let ((` we expect the name of a new symbols
                // which we do _not_ want to substitute with an existing entry from the symbol table
                if matches!(stack.last(), Some(Let(2))) {
                    stack.push(early_parse_single_token(ctx, None, value)?);
                } else {
                    // we eagerly parse expressions and types that are represented by a single token
                    stack.push(early_parse_single_token(ctx, Some(st), value)?);
                }
            }
            Token::EscapedValue(value) => {
                if orphan_closing_count > 0 {
                    return Err(SmtParserError::ClosingParenWithoutOpening);
                }
                stack.push(PExpr(lookup_sym(st, value)?))
            }
            Token::StringLit(value) => {
                let value = string_lit_to_string(value);
                todo!("unexpected string literal in expression: {value}")
            }
            Token::Comment(_) => {} // ignore comments
        }

        // are we done?
        match stack.as_slice() {
            [PExpr(e)] => return Ok(ExprOrType::E(*e)),
            [PType(t)] => return Ok(ExprOrType::T(*t)),
            _ => {} // cotinue parsing
        }
    }
    todo!("error message!: {stack:?}")
}

/// Extracts the value expression from SMT solver responses of the form ((... value))
/// We expect value to be self contained and thus no symbol table should be necessary.
pub fn parse_get_value_response(ctx: &mut Context, input: &[u8]) -> Result<ExprRef> {
    let mut lexer = Lexer::new(input);

    // skip `(`, `(` and first expression
    skip_open_parens(&mut lexer)?;
    skip_open_parens(&mut lexer)?;
    skip_expr(&mut lexer)?;

    // parse next expr
    let st = FxHashMap::default();
    let mut nested = NestedSymbolTable::new(&st);
    let expr = parse_expr_internal(ctx, &mut nested, &mut lexer)?;
    skip_close_parens(&mut lexer)?;
    skip_close_parens(&mut lexer)?;
    Ok(expr)
}

fn skip_open_parens(lexer: &mut Lexer) -> Result<()> {
    let token = lexer.next_no_comment();
    if token == Some(Token::Open) {
        Ok(())
    } else {
        Err(SmtParserError::MissingOpen(format!("{token:?}")))
    }
}

fn skip_close_parens(lexer: &mut Lexer) -> Result<()> {
    let token = lexer.next_no_comment();
    if token == Some(Token::Close) {
        Ok(())
    } else {
        Err(SmtParserError::MissingClose(format!("{token:?}")))
    }
}

/// Parses a single command.
pub fn parse_command(ctx: &mut Context, st: &SymbolTable, input: &[u8]) -> Result<SmtCommand> {
    let mut lexer = Lexer::new(input);
    // `(`
    skip_open_parens(&mut lexer)?;

    // next token should be the command
    let cmd_token = lexer.next_no_comment();
    let cmd = match cmd_token {
        Some(Token::Value(name)) => match name {
            b"exit" => SmtCommand::Exit,
            b"check-sat" => SmtCommand::CheckSat,
            b"set-logic" => {
                let logic = parse_logic(&mut lexer)?;
                SmtCommand::SetLogic(logic)
            }
            b"set-option" | b"set-info" => {
                let key = value_token(&mut lexer)?;
                let value = any_string_token(&mut lexer)?;
                if let Some(key) = key.strip_prefix(b":") {
                    let key = String::from_utf8_lossy(key).into();
                    if name == b"set-option" {
                        SmtCommand::SetOption(key, value.into())
                    } else {
                        debug_assert_eq!(name, b"set-info");
                        SmtCommand::SetInfo(key, value.into())
                    }
                } else {
                    return Err(SmtParserError::InvalidOptionKey(
                        String::from_utf8_lossy(key).into(),
                    ));
                }
            }
            b"assert" => {
                let mut nested = NestedSymbolTable::new(st);
                let expr = parse_expr_internal(ctx, &mut nested, &mut lexer)?;
                SmtCommand::Assert(expr)
            }
            b"declare-const" => {
                let name = String::from_utf8_lossy(value_token(&mut lexer)?);
                let mut nested = NestedSymbolTable::new(st);
                let tpe = parse_type(ctx, &mut nested, &mut lexer)?;
                let name_ref = ctx.string(name);
                let sym = ctx.symbol(name_ref, tpe);
                SmtCommand::DeclareConst(sym)
            }
            b"declare-fun" => {
                // parses the `declare-const` subset (i.e. no arguments!)
                let name = String::from_utf8_lossy(value_token(&mut lexer)?);
                skip_open_parens(&mut lexer)?;
                skip_close_parens(&mut lexer)?;
                let mut nested = NestedSymbolTable::new(st);
                let tpe = parse_type(ctx, &mut nested, &mut lexer)?;
                let name_ref = ctx.string(name);
                let sym = ctx.symbol(name_ref, tpe);
                SmtCommand::DeclareConst(sym)
            }
            b"define-const" => {
                let name = String::from_utf8_lossy(value_token(&mut lexer)?);
                let mut nested = NestedSymbolTable::new(st);
                let tpe = parse_type(ctx, &mut nested, &mut lexer)?;
                let value = parse_expr_internal(ctx, &mut nested, &mut lexer)?;
                // TODO: turn this into a proper error
                debug_assert_eq!(ctx[value].get_type(ctx), tpe);
                let name_ref = ctx.string(name);
                let sym = ctx.symbol(name_ref, tpe);
                SmtCommand::DefineConst(sym, value)
            }
            b"define-fun" => {
                // parses the `define-const` subset (i.e. no arguments!)
                let name = String::from_utf8_lossy(value_token(&mut lexer)?);
                skip_open_parens(&mut lexer)?;
                skip_close_parens(&mut lexer)?;
                let mut nested = NestedSymbolTable::new(st);
                let tpe = parse_type(ctx, &mut nested, &mut lexer)?;
                let value = parse_expr_internal(ctx, &mut nested, &mut lexer)?;
                // TODO: turn this into a proper error
                debug_assert_eq!(ctx[value].get_type(ctx), tpe);
                let name_ref = ctx.string(name);
                let sym = ctx.symbol(name_ref, tpe);
                SmtCommand::DefineConst(sym, value)
            }
            b"check-sat-assuming" => {
                let mut nested = NestedSymbolTable::new(st);
                let expressions = vec![parse_expr_internal(ctx, &mut nested, &mut lexer)?];
                // TODO: deal with more than one expression
                SmtCommand::CheckSatAssuming(expressions)
            }
            b"push" | b"pop" => {
                let n = value_token(&mut lexer)?;
                let n: u64 = String::from_utf8_lossy(n).parse()?;
                if name == b"push" {
                    SmtCommand::Push(n)
                } else {
                    SmtCommand::Pop(n)
                }
            }
            b"get-value" => {
                let mut nested = NestedSymbolTable::new(st);
                let expr = parse_expr_internal(ctx, &mut nested, &mut lexer)?;
                SmtCommand::GetValue(expr)
            }
            _ => {
                return Err(SmtParserError::UnknownCommand(format!(
                    "{}",
                    String::from_utf8_lossy(name)
                )));
            }
        },
        _ => return Err(SmtParserError::ExpectedCommand(format!("{cmd_token:?}"))),
    };

    // `)`
    skip_close_parens(&mut lexer)?;
    Ok(cmd)
}

fn parse_logic(lexer: &mut Lexer) -> Result<Logic> {
    match value_token(lexer)? {
        b"QF_BV" => Ok(Logic::QfBv),
        b"QF_ABV" => Ok(Logic::QfAbv),
        b"QF_AUFBV" => Ok(Logic::QfAufbv),
        b"ALL" => Ok(Logic::All),
        other => Err(SmtParserError::UnknownLogic(
            String::from_utf8_lossy(other).into(),
        )),
    }
}

fn value_token<'a>(lexer: &mut Lexer<'a>) -> Result<&'a [u8]> {
    match lexer.next_no_comment() {
        Some(Token::Value(v)) => Ok(v),
        Some(Token::EscapedValue(v)) => Ok(v),
        other => Err(SmtParserError::ExpectedIdentifer(format!("{other:?}"))),
    }
}

/// parse a token that can be converted to a string
fn any_string_token<'a>(lexer: &mut Lexer<'a>) -> Result<std::borrow::Cow<'a, str>> {
    match lexer.next_no_comment() {
        Some(Token::Value(v)) => Ok(String::from_utf8_lossy(v)),
        Some(Token::EscapedValue(v)) => Ok(String::from_utf8_lossy(v)),
        Some(Token::StringLit(v)) => Ok(string_lit_to_string(v).into()),
        other => Err(SmtParserError::ExpectedIdentifer(format!("{other:?}"))),
    }
}

fn skip_expr(lexer: &mut Lexer) -> Result<()> {
    let mut open_count = 0u64;
    for token in lexer.by_ref() {
        match token {
            Token::Open => {
                open_count += 1;
            }
            Token::Close => {
                open_count -= 1;
                if open_count == 0 {
                    return Ok(());
                }
            }
            Token::Comment(_) => {} // skip
            _ => {
                if open_count == 0 {
                    return Ok(());
                }
            }
        }
    }
    // reached end of tokens
    Err(SmtParserError::ExpectedExpr(
        "not an expression".to_string(),
    ))
}

fn lookup_sym(st: &mut NestedSymbolTable, name: &[u8]) -> Result<ExprRef> {
    let name = std::str::from_utf8(name)?;
    match st.get(name) {
        Some(s) => Ok(s),
        None => Err(SmtParserError::UnknownSymbol(name.to_string())),
    }
}

fn parse_pattern<'a>(
    ctx: &mut Context,
    st: &mut NestedSymbolTable,
    pattern: &[ParserItem<'a>],
) -> Result<ParserItem<'a>> {
    use NAry::*;
    use ParserItem::*;

    let item = match pattern {
        // an already parsed expression that just got pattern matches
        // (this can happen for simple expressions)
        [PExpr(e)] => PExpr(*e),
        ///////////////////////////////////////////////////////////////////////////////////////////
        // Expressions
        ///////////////////////////////////////////////////////////////////////////////////////////
        // BVSymbol is handled inside the `expr` function
        // BVLiteral is handled in the early parsing
        [ZExt(by), e] => PExpr(ctx.zero_extend(expr(st, e)?, *by)),
        [SExt(by), e] => PExpr(ctx.sign_extend(expr(st, e)?, *by)),
        [Extract(hi, lo), e] => PExpr(ctx.slice(expr(st, e)?, *hi, *lo)),
        [Sym(b"not"), e] => PExpr(ctx.not(expr(st, e)?)),
        [Sym(b"bvnot"), e] => PExpr(ctx.not(expr(st, e)?)),
        [Sym(b"bvneg"), e] => PExpr(ctx.negate(expr(st, e)?)),
        [Sym(b"="), args @ ..] => bin_op(st, "equal", args, |a, b| ctx.equal(a, b), Chainable)?,
        [Sym(b"=>"), args @ ..] => {
            bin_op(st, "implies", args, |a, b| ctx.implies(a, b), RightAssoc)?
        }
        [Sym(b"bvugt"), args @ ..] => {
            bin_op(st, "greater", args, |a, b| ctx.greater(a, b), Binary)?
        }
        [Sym(b"bvsgt"), args @ ..] => bin_op(
            st,
            "greater_signed",
            args,
            |a, b| ctx.greater_signed(a, b),
            Binary,
        )?,
        [Sym(b"bvuge"), args @ ..] => bin_op(
            st,
            "greater_or_equal",
            args,
            |a, b| ctx.greater_or_equal(a, b),
            Binary,
        )?,
        [Sym(b"bvsge"), args @ ..] => bin_op(
            st,
            "greater_or_equal_signed",
            args,
            |a, b| ctx.greater_or_equal_signed(a, b),
            Binary,
        )?,
        [Sym(b"concat"), args @ ..] => bin_op(st, "concat", args, |a, b| ctx.concat(a, b), Binary)?,
        [Sym(b"and"), args @ ..] => bin_op(st, "and", args, |a, b| ctx.and(a, b), LeftAssoc)?,
        [Sym(b"bvand"), args @ ..] => bin_op(st, "bvand", args, |a, b| ctx.and(a, b), LeftAssoc)?,
        [Sym(b"or"), args @ ..] => bin_op(st, "or", args, |a, b| ctx.or(a, b), LeftAssoc)?,
        [Sym(b"bvor"), args @ ..] => bin_op(st, "bvor", args, |a, b| ctx.or(a, b), LeftAssoc)?,
        [Sym(b"xor"), args @ ..] => bin_op(st, "xor", args, |a, b| ctx.xor(a, b), LeftAssoc)?,
        [Sym(b"bvxor"), args @ ..] => bin_op(st, "bvxor", args, |a, b| ctx.xor(a, b), LeftAssoc)?,
        [Sym(b"bvshl"), args @ ..] => {
            bin_op(st, "bvshl", args, |a, b| ctx.shift_left(a, b), Binary)?
        }
        [Sym(b"bvashr"), args @ ..] => bin_op(
            st,
            "bvashr",
            args,
            |a, b| ctx.arithmetic_shift_right(a, b),
            Binary,
        )?,
        [Sym(b"bvlshr"), args @ ..] => {
            bin_op(st, "bvlshr", args, |a, b| ctx.shift_right(a, b), Binary)?
        }
        [Sym(b"bvadd"), args @ ..] => bin_op(st, "bvadd", args, |a, b| ctx.add(a, b), LeftAssoc)?,
        [Sym(b"bvmul"), args @ ..] => bin_op(st, "bvmul", args, |a, b| ctx.mul(a, b), LeftAssoc)?,
        [Sym(b"bvsdiv"), args @ ..] => {
            bin_op(st, "bvsdiv", args, |a, b| ctx.signed_div(a, b), Binary)?
        }
        [Sym(b"bvudiv"), args @ ..] => bin_op(st, "bvudiv", args, |a, b| ctx.div(a, b), Binary)?,
        [Sym(b"bvsmod"), args @ ..] => {
            bin_op(st, "bvsmod", args, |a, b| ctx.signed_mod(a, b), Binary)?
        }
        [Sym(b"bvsrem"), args @ ..] => bin_op(
            st,
            "bvsrem",
            args,
            |a, b| ctx.signed_remainder(a, b),
            Binary,
        )?,
        [Sym(b"bvurem"), args @ ..] => {
            bin_op(st, "bvurem", args, |a, b| ctx.remainder(a, b), Binary)?
        }
        [Sym(b"bvsub"), args @ ..] => bin_op(st, "bvsub", args, |a, b| ctx.sub(a, b), Binary)?,
        [Sym(b"select"), PExpr(array), PExpr(index)] => PExpr(ctx.array_read(*array, *index)),
        [Sym(b"ite"), PExpr(cond), PExpr(t), PExpr(f)] => PExpr(ctx.ite(*cond, *t, *f)),
        // ArraySymbol is handled inside of `expr`
        [AsConst(tpe), PExpr(data)] => {
            debug_assert_eq!(tpe.data_width, data.get_bv_type(ctx).unwrap());
            PExpr(ctx.array_const(*data, tpe.index_width))
        }
        // ArrayEqual is handled above with the bv equal
        [Sym(b"store"), PExpr(array), PExpr(index), PExpr(data)] => {
            PExpr(ctx.array_store(*array, *index, *data))
        }
        // ArrayIte is handled above with the bv ite

        ///////////////////////////////////////////////////////////////////////////////////////////
        // Expressions that are not directly represented in our IR
        ///////////////////////////////////////////////////////////////////////////////////////////
        [Sym(b"bvult"), args @ ..] => bin_op(st, "bvult", args, |a, b| ctx.greater(b, a), Binary)?,
        [Sym(b"bvslt"), args @ ..] => {
            bin_op(st, "bvslt", args, |a, b| ctx.greater_signed(b, a), Binary)?
        }
        [Sym(b"distinct"), args @ ..] => bin_op(
            st,
            "distinct",
            args,
            |a, b| ctx.build(|c| c.not(c.equal(b, a))),
            Pairwise,
        )?,

        ///////////////////////////////////////////////////////////////////////////////////////////
        // Types
        ///////////////////////////////////////////////////////////////////////////////////////////
        [Sym(b"_"), Sym(b"BitVec"), Sym(width)] => PType(Type::BV(parse_width(width)?)),
        [
            Sym(b"Array"),
            PType(Type::BV(index_width)),
            PType(Type::BV(data_width)),
        ] => PType(Type::Array(ArrayType {
            index_width: *index_width,
            data_width: *data_width,
        })),

        ///////////////////////////////////////////////////////////////////////////////////////////
        // Parameterized Ops
        ///////////////////////////////////////////////////////////////////////////////////////////
        [Sym(b"as"), Sym(b"const"), PType(Type::Array(tpe))] => AsConst(*tpe),
        [Sym(b"_"), Sym(b"zero_extend"), Sym(by)] => ZExt(parse_width(by)?),
        [Sym(b"_"), Sym(b"sign_extend"), Sym(by)] => SExt(parse_width(by)?),
        [Sym(b"_"), Sym(b"extract"), Sym(hi), Sym(lo)] => {
            Extract(parse_width(hi)?, parse_width(lo)?)
        }
        // Let Definitions
        [Let(2), Sym(name), PExpr(value)] => {
            let name = std::str::from_utf8(name)?;
            st.push_let(name.into(), *value);
            // consume definition and implicit `)` token
            LetScopeOpenMissingClose
        }
        other => {
            return Err(SmtParserError::Pattern(format!("{other:?}")));
        }
    };
    Ok(item)
}

fn bin_op<'a>(
    st: &mut NestedSymbolTable,
    name: &str,
    args: &[ParserItem<'a>],
    mut op: impl FnMut(ExprRef, ExprRef) -> ExprRef,
    n_ary: NAry,
) -> Result<ParserItem<'a>> {
    if args.len() < 2 {
        return Err(SmtParserError::MissingArgs(
            name.to_string(),
            2,
            args.len() as u16,
        ));
    }
    match n_ary {
        NAry::LeftAssoc => {
            let args: Result<Vec<ExprRef>> = args.iter().map(|a| expr(st, a)).collect();
            let res = args?.into_iter().reduce(op).unwrap();
            Ok(ParserItem::PExpr(res))
        }
        _ => {
            // binary
            match args {
                [a, b] => Ok(ParserItem::PExpr(op(expr(st, a)?, expr(st, b)?))),
                _ => Err(SmtParserError::TooManyArgs(
                    name.to_string(),
                    2,
                    args.len() as u16,
                )),
            }
        }
    }
}

/// SMTLib defines several n-ary ops:
///
/// (=> Bool Bool Bool :right-assoc)
/// (=> x y z) <-> (=> x (=> y z))
///
/// (and Bool Bool Bool :left-assoc)
/// (and x y z) <-> (and (and x y) z)
///
/// (par (A) (= A A Bool :chainable))
/// (= x y z) <-> (and (= x y) (= y z))
///
/// (par (A) (distinct A A Bool :pairwise))
/// (distinct x y z) <-> (and (distinct x y) (distinct x z) (distinct y z))
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum NAry {
    Binary,
    RightAssoc,
    LeftAssoc,
    Chainable,
    Pairwise,
}

fn parse_width(value: &[u8]) -> Result<WidthInt> {
    Ok(std::str::from_utf8(value)?.parse()?)
}

/// errors if the item cannot be directly converted to an expression
fn expr(st: &mut NestedSymbolTable, item: &ParserItem<'_>) -> Result<ExprRef> {
    match item {
        ParserItem::PExpr(e) => Ok(*e),
        ParserItem::Sym(name) => lookup_sym(st, name),
        other => Err(SmtParserError::ExpectedExpr(format!("{other:?}"))),
    }
}

/// Parses things that can be represented by a single token.
fn early_parse_single_token<'a>(
    ctx: &mut Context,
    st: Option<&mut NestedSymbolTable>,
    value: &'a [u8],
) -> Result<ParserItem<'a>> {
    if let Some(match_id) = NUM_LIT_REGEX.matches(value).into_iter().next() {
        match match_id {
            0 => {
                // binary
                let value = baa::BitVecValue::from_bit_str(std::str::from_utf8(&value[2..])?)?;
                Ok(ParserItem::PExpr(ctx.bv_lit(&value)))
            }
            1 => {
                // hex
                let value = baa::BitVecValue::from_hex_str(std::str::from_utf8(&value[2..])?)?;
                Ok(ParserItem::PExpr(ctx.bv_lit(&value)))
            }
            2 => Err(SmtParserError::Unsupported(format!(
                "decimal constant: {}",
                String::from_utf8_lossy(value)
            ))),
            3 => Ok(ParserItem::PExpr(ctx.get_true())),
            4 => Ok(ParserItem::PExpr(ctx.get_false())),
            _ => unreachable!("not part of the regex!"),
        }
    } else {
        match value {
            b"Bool" => Ok(ParserItem::PType(Type::BV(1))),
            b"let" => Ok(ParserItem::Let(0)),
            other => {
                let symbol = st
                    .and_then(|st| lookup_sym(st, other).ok())
                    .map(ParserItem::PExpr);
                Ok(symbol.unwrap_or(ParserItem::Sym(value)))
            }
        }
    }
}

/// represents intermediate parser results
enum ParserItem<'a> {
    /// `Open(false)`: opening parenthesis, `Open(true)`: `(let (( ... ))` scope start
    Open(bool),
    /// parsed expression
    PExpr(ExprRef),
    /// parsed type
    PType(Type),
    /// either a built-in or a user defined symbol
    Sym(&'a [u8]),
    /// as const function from the array theory
    AsConst(ArrayType),
    /// zero extend function
    ZExt(WidthInt),
    /// sign extend function
    SExt(WidthInt),
    /// extract (aka slice) function
    Extract(WidthInt, WidthInt),
    /// let expression w/ opening parenthesis count
    Let(u8),
    /// start of a let scope, e.g., `(let ((...)`
    LetScopeOpenMissingClose,
}

impl<'a> Debug for ParserItem<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserItem::Open(false) => write!(f, "("),
            ParserItem::PExpr(e) => write!(f, "{e:?}"),
            ParserItem::PType(t) => write!(f, "{t:?}"),
            ParserItem::Sym(v) => write!(f, "S({})", String::from_utf8_lossy(v)),
            ParserItem::AsConst(tpe) => write!(f, "AsConst({tpe:?})"),
            ParserItem::ZExt(by) => write!(f, "ZExt({by})"),
            ParserItem::SExt(by) => write!(f, "SExt({by})"),
            ParserItem::Extract(hi, lo) => write!(f, "Slice({hi}, {lo})"),
            ParserItem::Let(parens) => {
                write!(f, "let")?;
                for _ in 0..*parens {
                    write!(f, "(")?;
                }
                Ok(())
            }
            ParserItem::LetScopeOpenMissingClose => write!(f, "(let (( ... )"),
            ParserItem::Open(true) => write!(f, "(let (( ... ))"),
        }
    }
}

lazy_static! {
    static ref NUM_LIT_REGEX: RegexSet = RegexSet::new([
        r"^#b[01]+$",                    // binary
        r"^#x[[:xdigit:]]+$",            // hex
        r"^[[:digit:]]+\.[[:digit:]]+$", // decimal
        r"^true$",                       // true == 1
        r"^false$",                       // false == 0
    ]).unwrap();
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Lexer
////////////////////////////////////////////////////////////////////////////////////////////////////

struct Lexer<'a> {
    input: &'a [u8],
    state: LexState,
    pos: usize,
}

#[derive(Eq, PartialEq)]
enum Token<'a> {
    Open,
    Close,
    Value(&'a [u8]),
    EscapedValue(&'a [u8]),
    StringLit(&'a [u8]),
    Comment(&'a [u8]),
}

impl<'a> Debug for Token<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Open => write!(f, "("),
            Token::Close => write!(f, ")"),
            Token::Value(v) => write!(f, "{}", String::from_utf8_lossy(v)),
            Token::EscapedValue(v) => write!(f, "{}", String::from_utf8_lossy(v)),
            Token::StringLit(v) => write!(f, "{}", string_lit_to_string(v)),
            Token::Comment(v) => write!(f, "/* {} */", String::from_utf8_lossy(v)),
        }
    }
}

fn string_lit_to_string(value: &[u8]) -> String {
    let s = String::from_utf8_lossy(value);
    s.replace("\"\"", "\"")
}

#[derive(Debug, Copy, Clone)]
enum LexState {
    Searching,
    ParsingToken(usize),
    ParsingEscapedToken(usize),
    ParsingStringLiteral(usize),
    StringLiteralQuoteFound(usize),
    ParsingComment(usize),
}

impl<'a> Lexer<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            state: LexState::Searching,
            pos: 0,
        }
    }

    /// returns the next token that is not a comment
    fn next_no_comment(&mut self) -> Option<Token<'a>> {
        self.by_ref()
            .find(|token| !matches!(token, Token::Comment(_)))
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use LexState::*;

        // are we already done?
        if self.pos >= self.input.len() {
            return None;
        }

        for &c in self.input.iter().skip(self.pos) {
            match self.state {
                Searching => {
                    // when we are searching, we always consume the character
                    self.pos += 1;
                    self.state = match c {
                        b'|' => ParsingEscapedToken(self.pos),
                        b'(' => return Some(Token::Open),
                        b')' => return Some(Token::Close),
                        // White Space Characters: tab, line feed, carriage return or space
                        b' ' | b'\n' | b'\r' | b'\t' => Searching,
                        b'"' => ParsingStringLiteral(self.pos),
                        b';' => ParsingComment(self.pos),
                        _ => ParsingToken(self.pos - 1),
                    }
                }
                ParsingToken(start) => {
                    debug_assert!(start <= self.pos, "{start} > {}", self.pos);
                    match c {
                        // done
                        b'|' | b'(' | b')' | b' ' | b'\n' | b'\r' | b'\t' => {
                            self.state = Searching; // do not consume the character
                            return Some(Token::Value(&self.input[start..self.pos]));
                        }
                        _ => {
                            // consume character
                            self.pos += 1;
                        }
                    }
                }
                ParsingEscapedToken(start) => {
                    // consume character
                    self.pos += 1;
                    if c == b'|' {
                        self.state = Searching;
                        return Some(Token::EscapedValue(&self.input[start..(self.pos - 1)]));
                    }
                }
                ParsingStringLiteral(start) => {
                    // consume character
                    self.pos += 1;
                    if c == b'"' {
                        self.state = StringLiteralQuoteFound(start);
                    }
                }
                StringLiteralQuoteFound(start) => {
                    // did we just find an escaped quote?
                    if c == b'"' {
                        // consume character
                        self.pos += 1;
                        self.state = ParsingStringLiteral(start);
                    } else {
                        self.state = Searching; // do not consume the character
                        return Some(Token::StringLit(&self.input[start..(self.pos - 1)]));
                    }
                }
                ParsingComment(start) => {
                    if c == b'\n' || c == b'\r' {
                        self.state = Searching; // do not consume the character
                        return Some(Token::Comment(&self.input[start..(self.pos - 1)]));
                    } else {
                        // consume character
                        self.pos += 1;
                    }
                }
            };
        }

        // finish parsing at the end of string
        match self.state {
            ParsingToken(start) => {
                self.pos = self.input.len();
                Some(Token::Value(&self.input[start..self.pos]))
            }
            ParsingComment(start) => {
                self.pos = self.input.len();
                Some(Token::Comment(&self.input[start..self.pos]))
            }
            Searching => {
                debug_assert_eq!(
                    self.pos,
                    self.input.len(),
                    "{}",
                    String::from_utf8_lossy(self.input)
                );
                None
            }
            other => {
                todo!("smt lexer: handle being in state `{other:?}` at the end of the input");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::SerializableIrNode;
    use crate::smt::Logic;

    fn lex_to_token_str(input: &str) -> String {
        let tokens = Lexer::new(input.as_bytes())
            .map(|token| format!("{token:?}"))
            .collect::<Vec<_>>();
        tokens.join(" ")
    }

    #[test]
    fn test_lexer() {
        let inp = "(+ a b)";
        assert_eq!(lex_to_token_str(inp), "( + a b )");
        let inp = "(+ |a|    b     (      )";
        assert_eq!(lex_to_token_str(inp), "( + a b ( )");
    }

    #[test]
    fn test_parser() {
        let mut ctx = Context::default();
        let a = ctx.bv_symbol("a", 2);
        let symbols = FxHashMap::from_iter([("a".to_string(), a)]);
        let expr = parse_expr(&mut ctx, &symbols, "(bvand a #b00)".as_bytes()).unwrap();
        assert_eq!(expr, ctx.build(|c| c.and(a, c.bit_vec_val(0, 2))));
    }

    #[test]
    fn test_get_value_parser() {
        let mut ctx = Context::default();
        let expr = parse_get_value_response(&mut ctx, "((a #b011))".as_bytes()).unwrap();
        assert_eq!(expr, ctx.bit_vec_val(3, 3));

        // calling get-value on a more complext response
        let solver_response = "(((bvadd ((_ zero_extend 1) a) (ite false #b0001 #b0000)) #b0001))";
        let expr = parse_get_value_response(&mut ctx, solver_response.as_bytes()).unwrap();
        assert_eq!(expr, ctx.bit_vec_val(1, 4));
    }

    #[test]
    fn test_parse_smt_array_const_and_store() {
        let mut ctx = Context::default();
        let symbols = FxHashMap::default();

        let base =
            "((as const (Array (_ BitVec 5) (_ BitVec 32))) #b00000000000000000000000000110011)";
        let expr = parse_expr(&mut ctx, &symbols, base.as_bytes()).unwrap();
        assert_eq!(expr.serialize_to_str(&ctx), "([32'x00000033] x 2^5)");

        let store_1 = format!("(store {base} #b01110 #x00000000)");
        let expr = parse_expr(&mut ctx, &symbols, store_1.as_bytes()).unwrap();
        assert_eq!(
            expr.serialize_to_str(&ctx),
            "([32'x00000033] x 2^5)[5'b01110 := 32'x00000000]"
        );

        let store_2 = format!("(store {store_1} #b01110 #x00000011)");
        let expr = parse_expr(&mut ctx, &symbols, store_2.as_bytes()).unwrap();
        assert_eq!(
            expr.serialize_to_str(&ctx),
            "([32'x00000033] x 2^5)[5'b01110 := 32'x00000000][5'b01110 := 32'x00000011]"
        );
    }

    fn test_parse_expr(ctx: &mut Context, input: &str) -> Result<ExprRef> {
        let symbols = FxHashMap::default();
        parse_expr(ctx, &symbols, input.as_bytes())
    }

    #[test]
    fn test_parse_simple_expr() {
        let mut ctx = Context::default();
        let smt_expr = test_parse_expr(&mut ctx, "true").unwrap();
        assert!(ctx[smt_expr].is_true());
        let smt_expr = test_parse_expr(&mut ctx, "false").unwrap();
        assert!(ctx[smt_expr].is_false());
    }

    #[test]
    fn test_parse_let_expr() {
        let mut ctx = Context::default();
        let smt_expr = test_parse_expr(&mut ctx, "(let ((abc #b1)) abc)").unwrap();
        assert!(ctx[smt_expr].is_true());

        // test shadowing
        let smt_expr =
            test_parse_expr(&mut ctx, "(let ((abc #b1)) (let ((abc #b0)) abc))").unwrap();
        assert!(ctx[smt_expr].is_false());
    }

    #[test]
    fn test_parse_cmd() {
        let mut ctx = Context::default();
        let mut st = FxHashMap::default();

        // test lexer on simple exit command
        assert_eq!(
            parse_command(&mut ctx, &mut st, "(exit)".as_bytes()).unwrap(),
            SmtCommand::Exit
        );
        assert_eq!(
            parse_command(&mut ctx, &mut st, "(exit) ".as_bytes()).unwrap(),
            SmtCommand::Exit
        );
        assert_eq!(
            parse_command(&mut ctx, &mut st, "(exit )".as_bytes()).unwrap(),
            SmtCommand::Exit
        );
        assert_eq!(
            parse_command(&mut ctx, &mut st, "( exit)".as_bytes()).unwrap(),
            SmtCommand::Exit
        );
        assert_eq!(
            parse_command(&mut ctx, &mut st, " ( exit ) ".as_bytes()).unwrap(),
            SmtCommand::Exit
        );

        // check-sat
        assert_eq!(
            parse_command(&mut ctx, &mut st, "(check-sat)".as_bytes()).unwrap(),
            SmtCommand::CheckSat
        );

        // set-logic
        assert_eq!(
            parse_command(&mut ctx, &mut st, "(set-logic QF_AUFBV)".as_bytes()).unwrap(),
            SmtCommand::SetLogic(Logic::QfAufbv)
        );

        assert!(matches!(
            parse_command(&mut ctx, &mut st, "(set-logic AUFBV)".as_bytes())
                .err()
                .unwrap(),
            SmtParserError::UnknownLogic(_)
        ));

        // set-option
        assert_eq!(
            parse_command(&mut ctx, &mut st, "(set-option :a b)".as_bytes()).unwrap(),
            SmtCommand::SetOption("a".to_string(), "b".to_string())
        );

        assert!(matches!(
            parse_command(&mut ctx, &mut st, "(set-option a b)".as_bytes())
                .err()
                .unwrap(),
            SmtParserError::InvalidOptionKey(_)
        ));
    }
}
