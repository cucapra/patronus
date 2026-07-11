use crate::expr::{Context, ExprRef, eval_expr};
use crate::mc::types::Result;
use crate::smt::{CheckSatResponse, SolverContext};
use baa::Value;
use rustc_hash::FxHashMap;

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
