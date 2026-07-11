use crate::expr::{
    Context, ExprRef, SerializableIrNode, StringRef, TypeCheck, simple_transform_expr,
};
use crate::mc::types::Result;
use crate::smt::SolverContext;
use crate::system::analysis::{Uses, analyze_for_serialization};
use crate::system::{State, TransitionSystem};
use rustc_hash::FxHashSet;

pub type Step = u64;

pub trait TransitionSystemEncoding {
    fn define_header(&self, smt_ctx: &mut impl SolverContext) -> Result<()>;
    fn init_at(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        step: u64,
    ) -> Result<()>;
    fn unroll(&mut self, ctx: &mut Context, smt_ctx: &mut impl SolverContext) -> Result<()>;
    /// Step SMT expression
    fn step_at(&self, ctx: &mut Context, expr: ExprRef, k: Step) -> ExprRef;
}

pub struct UnrollSmtEncoding {
    /// the offset at which our encoding was initialized
    offset: Option<u64>,
    current_step: Option<Step>,
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
        let max_ser_index: usize = ser_info
            .signal_order
            .iter()
            .map(|s| s.expr.into())
            .max()
            .unwrap_or_default();
        let max_state_index: usize = sys
            .states
            .iter()
            .map(|s| s.symbol.into())
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
                let default_name = format!("__n{}", usize::from(root.expr));
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
            signals[usize::from(root.expr)] = Some(info);
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
            signals[usize::from(state.symbol)] = Some(info);
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
        step: Step,
        filter: &impl Fn(&SmtSignalInfo) -> bool,
    ) -> Result<()> {
        for expr in self.signal_order.iter() {
            let info = self.signals[usize::from(*expr)].as_ref().unwrap();
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

    fn create_signal_symbols_in_step(&mut self, ctx: &mut Context, step: Step) {
        let offset = self.offset.expect("Need to call init_at first!");
        let index = (step - offset) as usize;
        assert_eq!(self.symbols_at.len(), index, "Missing or duplicate step!");
        let mut syms = Vec::with_capacity(self.signal_order.len());
        for &signal in self
            .signal_order
            .iter()
            .chain(self.states.iter().map(|s| &s.symbol))
        {
            let info = self.signals[usize::from(signal)].as_ref().unwrap();
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

    fn signal_sym_in_step(&self, expr: ExprRef, step: Step) -> Option<ExprRef> {
        if let Some(Some(info)) = self.signals.get(usize::from(expr)) {
            let offset = self.offset.expect("Need to call init_at first!");
            let index = (step - offset) as usize;
            Some(self.symbols_at[index][info.id as usize])
        } else {
            None
        }
    }

    fn expr_in_step(&self, ctx: &mut Context, expr: ExprRef, step: Step) -> ExprRef {
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
        step: Step,
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

    fn step_at(&self, ctx: &mut Context, expr: ExprRef, k: Step) -> ExprRef {
        assert!(k <= self.current_step.unwrap_or(0));

        self.signal_sym_in_step(expr, k).unwrap_or_else(|| {
            if ctx[expr].is_true() || ctx[expr].is_false() {
                // If expression is a simple constant, return it
                expr
            } else if ctx[expr].is_symbol() {
                // If expression is itself an atomic symbol, it could not be found
                panic!(
                    "Failed to find signal {} in step {k}",
                    expr.serialize_to_str(ctx)
                );
            } else {
                // `expr` must be compound expression: recursively step all symbols
                simple_transform_expr(ctx, expr, |ctx, e, _| {
                    if ctx[e].is_symbol() {
                        Some(self.step_at(ctx, e, k))
                    } else {
                        None
                    }
                })
            }
        })
    }
}

fn name_at(name: &str, step: Step) -> String {
    format!("{}@{}", name, step)
}
