// Copyright 2023 The Regents of the University of California
// Copyright 2024-2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::*;
use crate::mc::Witness;
use crate::mc::types::InitValue;
use crate::smt::*;
use crate::system::analysis::{UseCountInt, Uses, analyze_for_serialization, count_expr_uses};
use crate::system::{State, TransitionSystem};
use baa::*;
use rustc_hash::{FxHashMap, FxHashSet};

type Result<T> = crate::smt::Result<T>;

/// Runs up to [k_max] steps of BMC.
///
/// * [check_constraints] perform additional checking to ensure that
///   the assumptions are satisfiable.
/// * [check_bad_states_individually] perform one SMT solver check per assertion instead of
///   combining them into a single check.
pub fn bmc(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    sys: &TransitionSystem,
    check_constraints: bool,
    check_bad_states_individually: bool,
    k_max: u64,
) -> Result<ModelCheckResult> {
    assert!(k_max > 0 && k_max <= 2000, "unreasonable k_max={}", k_max);

    let mut enc = match start_bmc_or_pdr(ctx, smt_ctx, sys)? {
        (r, None) => return Ok(r),
        (_, Some(enc)) => enc,
    };
    enc.init_at(ctx, smt_ctx, 0)?;

    let constraints = sys.constraints.clone();
    let bad_states = sys.bad_states.clone();

    for k in 0..=k_max {
        // assume all constraints hold in this step
        for expr_ref in constraints.iter() {
            let expr = enc.get_at(ctx, *expr_ref, k);
            smt_ctx.assert(ctx, expr)?;
        }

        // make sure the constraints are not contradictory
        if check_constraints {
            let res = smt_ctx.check_sat()?;
            assert_eq!(
                res,
                CheckSatResponse::Sat,
                "Found unsatisfiable constraints in cycle {}",
                k
            );
        }

        if check_bad_states_individually {
            for expr_ref in bad_states.iter() {
                let expr = enc.get_at(ctx, *expr_ref, k);
                let res = check_assuming(ctx, smt_ctx, [expr])?;

                // count expression uses
                let use_counts = count_expr_uses(ctx, sys);
                if res == CheckSatResponse::Sat {
                    let wit = get_witness(sys, ctx, &use_counts, smt_ctx, &enc, k, &bad_states)?;
                    return Ok(ModelCheckResult::Fail(wit));
                }
                check_assuming_end(smt_ctx)?;
            }
        } else {
            let all_bads = bad_states
                .iter()
                .map(|expr_ref| enc.get_at(ctx, *expr_ref, k))
                .collect::<Vec<_>>();
            let any_bad = all_bads.into_iter().reduce(|a, b| ctx.or(a, b)).unwrap();
            let res = check_assuming(ctx, smt_ctx, [any_bad])?;

            // count expression uses
            let use_counts = count_expr_uses(ctx, sys);
            if res == CheckSatResponse::Sat {
                let wit = get_witness(sys, ctx, &use_counts, smt_ctx, &enc, k, &bad_states)?;
                return Ok(ModelCheckResult::Fail(wit));
            }
            check_assuming_end(smt_ctx)?;
        }

        // advance
        enc.unroll(ctx, smt_ctx)?;
    }

    // we have not found any assertion violations
    Ok(ModelCheckResult::Success)
}

pub(crate) fn start_bmc_or_pdr<S: SolverContext>(
    ctx: &mut Context,
    smt_ctx: &mut S,
    sys: &TransitionSystem,
) -> Result<(
    ModelCheckResult,
    Option<impl TransitionSystemEncoding + use<S>>,
)> {
    // if there are no assertions, there cannot be an error!
    if sys.bad_states.is_empty() {
        return Ok((ModelCheckResult::Success, None));
    }

    // z3 only supports the non-standard as-const array syntax when the logic is set to ALL
    let logic = if smt_ctx.name() == "z3" {
        Logic::All
    } else if smt_ctx.supports_uf() {
        Logic::QfAufbv
    } else {
        Logic::QfAbv
    };
    smt_ctx.set_logic(logic)?;

    // TODO: maybe add support for the more compact SMT encoding
    let enc = UnrollSmtEncoding::new(ctx, sys, false);
    enc.define_header(smt_ctx)?;

    Ok((ModelCheckResult::Unknown, Some(enc)))
}

#[allow(clippy::too_many_arguments)]
fn get_witness(
    sys: &TransitionSystem,
    ctx: &mut Context,
    _use_counts: &[UseCountInt], // TODO: analyze array expressions in order to record which indices are accessed
    smt_ctx: &mut impl SolverContext,
    enc: &impl TransitionSystemEncoding,
    k_max: u64,
    bad_states: &[ExprRef],
) -> Result<Witness> {
    let mut wit = Witness::default();

    // which bad states did we hit?
    for (bad_idx, expr) in bad_states.iter().enumerate() {
        let sym_at = enc.get_at(ctx, *expr, k_max);
        let value = get_smt_value(ctx, smt_ctx, sym_at)?;
        let value = match value {
            Value::Array(_) => unreachable!("should always be a bitvector!"),
            Value::BitVec(v) => v,
        };
        if !value.is_zero() {
            // was the bad state condition fulfilled?
            wit.failed_safety.push(bad_idx as u32);
        }
    }

    // collect initial values
    for (state_cnt, state) in sys.states.iter().enumerate() {
        let sym_at = enc.get_at(ctx, state.symbol, 0);
        let value = get_smt_value(ctx, smt_ctx, sym_at)?;
        // we assume that state ids are monotonically increasing with +1
        assert_eq!(wit.init.len(), state_cnt);
        // convert to a witness value
        let wit_value = match value {
            Value::Array(v) => {
                // TODO: narrow down the relevant indices
                let indices = (0..v.num_elements())
                    .map(|ii| BitVecValue::from_u64(ii as u64, v.index_width()))
                    .collect::<Vec<_>>();
                InitValue::Array(v, indices)
            }
            Value::BitVec(v) => InitValue::BitVec(v),
        };
        wit.init.push(wit_value);
        // also save state name
        wit.init_names
            .push(Some(ctx.get_symbol_name(state.symbol).unwrap().to_string()))
    }

    // save input names
    for input in sys.inputs.iter() {
        wit.input_names
            .push(Some(ctx.get_symbol_name(*input).unwrap().to_string()));
    }

    for k in 0..=k_max {
        let mut input_values = Vec::default();
        for input in sys.inputs.iter() {
            let sym_at = enc.get_at(ctx, *input, k);
            let value = get_smt_value(ctx, smt_ctx, sym_at)?;
            input_values.push(Some(value));
        }
        wit.inputs.push(input_values);
    }

    Ok(wit)
}

#[inline]
pub fn check_assuming(
    ctx: &Context,
    smt_ctx: &mut impl SolverContext,
    props: impl IntoIterator<Item = ExprRef>,
) -> Result<CheckSatResponse> {
    if smt_ctx.supports_check_assuming() {
        smt_ctx.check_sat_assuming(ctx, props)
    } else {
        smt_ctx.push()?; // add new assertion
        for prop in props.into_iter() {
            smt_ctx.assert(ctx, prop)?;
        }
        let res = smt_ctx.check_sat()?;
        Ok(res)
    }
}

// pops context for solver that do not support check assuming
#[inline]
pub fn check_assuming_end(smt_ctx: &mut impl SolverContext) -> Result<()> {
    if !smt_ctx.supports_check_assuming() {
        smt_ctx.pop()
    } else {
        Ok(())
    }
}

pub fn get_smt_value(
    ctx: &mut Context,
    smt_ctx: &mut impl SolverContext,
    expr: ExprRef,
) -> Result<Value> {
    let value_expr = smt_ctx.get_value(ctx, expr)?;
    let value = eval_expr(ctx, &FxHashMap::default(), value_expr);
    Ok(value)
}

pub enum ModelCheckResult {
    Success,
    Unknown,
    Fail(Witness),
}

pub trait TransitionSystemEncoding {
    fn define_header(&self, smt_ctx: &mut impl SolverContext) -> Result<()>;
    fn init_at(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        step: u64,
    ) -> Result<()>;
    fn unroll(&mut self, ctx: &mut Context, smt_ctx: &mut impl SolverContext) -> Result<()>;
    /// Allows access to inputs, states, constraints and bad_state expressions.
    fn get_at(&self, ctx: &Context, expr: ExprRef, k: u64) -> ExprRef;
}

pub struct UnrollSmtEncoding {
    /// the offset at which our encoding was initialized
    offset: Option<u64>,
    current_step: Option<u64>,
    /// all signals that need to be serialized separately, in the correct order
    signal_order: Vec<ExprRef>,
    /// look up table to see if an expression is a reference
    signals: Vec<Option<SmtSignalInfo>>,
    /// system states
    states: Vec<State>,
    /// symbols of signals at every step
    symbols_at: Vec<Vec<ExprRef>>,
}

#[derive(Clone)]
struct SmtSignalInfo {
    /// monotonically increasing unique id
    id: u16,
    name: StringRef,
    uses: Uses,
    is_state: bool,
    is_input: bool,
    /// denotes states that do not change and thus can be represented by a single symbol
    is_const: bool,
}

impl UnrollSmtEncoding {
    pub fn new(ctx: &mut Context, sys: &TransitionSystem, include_outputs: bool) -> Self {
        let ser_info = analyze_for_serialization(ctx, sys, include_outputs);
        let max_ser_index = ser_info
            .signal_order
            .iter()
            .map(|s| s.expr.index())
            .max()
            .unwrap_or_default();
        let max_state_index = sys
            .states
            .iter()
            .map(|s| s.symbol.index())
            .max()
            .unwrap_or_default();
        let signals_map_len = std::cmp::max(max_ser_index, max_state_index) + 1;
        let mut signals = vec![None; signals_map_len];
        let mut signal_order = Vec::with_capacity(ser_info.signal_order.len());

        let is_state: FxHashSet<ExprRef> =
            FxHashSet::from_iter(sys.states.iter().map(|s| s.symbol));

        // we skip states in our signal order since they are not calculated directly in the update function
        let input_set = FxHashSet::from_iter(sys.inputs.iter().cloned());
        for (id, root) in ser_info
            .signal_order
            .into_iter()
            .filter(|r| !is_state.contains(&r.expr))
            .enumerate()
        {
            signal_order.push(root.expr);
            let name = sys.names[root.expr].unwrap_or({
                let default_name = format!("__n{}", root.expr.index());
                ctx.string(default_name.into())
            });
            let is_input = input_set.contains(&root.expr);
            let info = SmtSignalInfo {
                id: id as u16,
                name,
                uses: root.uses,
                is_state: false,
                is_input,
                is_const: false,
            };
            signals[root.expr.index()] = Some(info);
        }
        for (id, state) in sys.states.iter().enumerate() {
            let id = (id + signal_order.len()) as u16;
            let info = SmtSignalInfo {
                id,
                name: ctx[state.symbol].get_symbol_name_ref().unwrap(),
                uses: Uses::default(), // irrelevant
                is_state: true,
                is_input: false,
                is_const: state.is_const(),
            };
            signals[state.symbol.index()] = Some(info);
        }
        let current_step = None;
        let offset = None;
        let states = sys.states.clone();

        Self {
            offset,
            current_step,
            signals,
            signal_order,
            states,
            symbols_at: Vec::new(),
        }
    }

    fn define_signals(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        step: u64,
        filter: &impl Fn(&SmtSignalInfo) -> bool,
    ) -> Result<()> {
        for expr in self.signal_order.iter() {
            let info = self.signals[expr.index()].as_ref().unwrap();
            if info.is_state {
                continue;
            }
            let skip = !filter(info);
            if !skip {
                let tpe = expr.get_type(ctx);
                let name = ctx.string(name_at(&ctx[info.name], step).into());
                let symbol_at = ctx.symbol(name, tpe);
                if ctx[*expr].is_symbol() {
                    smt_ctx.declare_const(ctx, symbol_at)?;
                } else {
                    let value = self.expr_in_step(ctx, *expr, step);
                    smt_ctx.define_const(ctx, symbol_at, value)?;
                }
            }
        }
        Ok(())
    }

    fn create_signal_symbols_in_step(&mut self, ctx: &mut Context, step: u64) {
        let offset = self.offset.expect("Need to call init_at first!");
        let index = (step - offset) as usize;
        assert_eq!(self.symbols_at.len(), index, "Missing or duplicate step!");
        let mut syms = Vec::with_capacity(self.signal_order.len());
        for signal in self
            .signal_order
            .iter()
            .chain(self.states.iter().map(|s| &s.symbol))
        {
            let info = self.signals[signal.index()].as_ref().unwrap();
            let name_ref = if info.is_const {
                info.name
            } else {
                let name = name_at(&ctx[info.name], step);
                ctx.string(name.into())
            };
            let tpe = signal.get_type(ctx);
            debug_assert_eq!(info.id as usize, syms.len());
            syms.push(ctx.symbol(name_ref, tpe));
        }
        self.symbols_at.push(syms);
    }

    fn signal_sym_in_step(&self, expr: ExprRef, step: u64) -> Option<ExprRef> {
        if let Some(Some(info)) = self.signals.get(expr.index()) {
            let offset = self.offset.expect("Need to call init_at first!");
            let index = (step - offset) as usize;
            Some(self.symbols_at[index][info.id as usize])
        } else {
            None
        }
    }

    fn expr_in_step(&self, ctx: &mut Context, expr: ExprRef, step: u64) -> ExprRef {
        let expr_is_symbol = ctx[expr].is_symbol();
        simple_transform_expr(ctx, expr, |_, e, _| {
            // If the expression we are trying to serialize is not a symbol, then wo
            // do not just want to replace it with one, as that would lead us to a tautology!
            if !expr_is_symbol && e == expr {
                None
            } else {
                self.signal_sym_in_step(e, step)
            }
        })
    }
}

impl TransitionSystemEncoding for UnrollSmtEncoding {
    fn define_header(&self, _smt_ctx: &mut impl SolverContext) -> Result<()> {
        // nothing to do in this encoding
        Ok(())
    }

    fn init_at(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        step: u64,
    ) -> Result<()> {
        // delete old mutable state
        self.symbols_at.clear();
        // remember current step and starting offset
        self.current_step = Some(step);
        self.offset = Some(step);
        self.create_signal_symbols_in_step(ctx, step);

        if step == 0 {
            // define signals that are used to calculate init expressions
            self.define_signals(ctx, smt_ctx, 0, &|info: &SmtSignalInfo| info.uses.init > 0)?;
        }

        // declare/define initial states
        for state in self.states.iter() {
            let symbol_at = if state.is_const() {
                state.symbol
            } else {
                let base_name = ctx.get_symbol_name(state.symbol).unwrap();
                let name = ctx.string(name_at(base_name, step).into());
                let tpe = state.symbol.get_type(ctx);
                ctx.symbol(name, tpe)
            };

            match (step, state.init) {
                (0, Some(value)) => {
                    let value_at = self.expr_in_step(ctx, value, step);
                    smt_ctx.define_const(ctx, symbol_at, value_at)?;
                }
                _ => {
                    smt_ctx.declare_const(ctx, symbol_at)?;
                }
            }
        }

        // define other signals including inputs, init signals are never needed here
        self.define_signals(ctx, smt_ctx, step, &|info: &SmtSignalInfo| {
            (info.uses.other > 0 || info.is_input) && (info.uses.init == 0)
        })?;

        Ok(())
    }

    fn unroll(&mut self, ctx: &mut Context, smt_ctx: &mut impl SolverContext) -> Result<()> {
        let prev_step = self.current_step.unwrap();
        let next_step = prev_step + 1;
        self.create_signal_symbols_in_step(ctx, next_step);

        // define next state signals for previous state
        self.define_signals(ctx, smt_ctx, prev_step, &|info: &SmtSignalInfo| {
            info.uses.next > 0 && info.uses.other == 0 && !info.is_input
        })?;

        // define next state
        for state in self.states.iter() {
            let name = name_at(ctx.get_symbol_name(state.symbol).unwrap(), next_step);
            let name = ctx.string(name.into());
            let tpe = state.symbol.get_type(ctx);
            let symbol_at = ctx.symbol(name, tpe);
            match state.next {
                Some(value) => {
                    // constant states never change from their initial value
                    if !state.is_const() {
                        let value = self.expr_in_step(ctx, value, prev_step);
                        smt_ctx.define_const(ctx, symbol_at, value)?;
                    }
                }
                None => {
                    smt_ctx.declare_const(ctx, symbol_at)?;
                }
            }
        }

        // define other signals and inputs
        // we always define all inputs, even if they are only used in the "next" expression
        // since our witness extraction relies on them being available
        self.define_signals(ctx, smt_ctx, next_step, &|info: &SmtSignalInfo| {
            info.uses.other > 0 || info.is_input
        })?;

        // update step count
        self.current_step = Some(next_step);
        Ok(())
    }

    fn get_at(&self, _ctx: &Context, expr: ExprRef, step: u64) -> ExprRef {
        assert!(step <= self.current_step.unwrap_or(0));
        self.signal_sym_in_step(expr, step).unwrap()
    }
}

fn name_at(name: &str, step: u64) -> String {
    format!("{}@{}", name, step)
}
