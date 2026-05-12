// Copyright 2024-2026 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Symbolic Expression Evaluation
//! Similar to the functionality in `[[patronus::expr::eval]]`, but working with
//! symbolic expressions instead of concrete values.

use crate::value_summary::{Value, ValueContext};
use crate::{GuardCtx, ValueSummary};
use baa::BitVecValue;
use patronus::expr::{Expr, ExprRef, ForEachChild};
use smallvec::SmallVec;
// type ValueStack = Vec<[ValueSummary<>]>

/// Returns a symbolic value for an expression if it is available.
pub trait GetExprValue<V: Value> {
    fn get(&self, expr: ExprRef) -> Option<&ValueSummary<V>>;
}

impl GetExprValue<ExprRef> for [(ExprRef, ValueSummary<ExprRef>)] {
    fn get(&self, expr: ExprRef) -> Option<&ValueSummary<ExprRef>> {
        self.iter()
            .find(|(key, _)| *key == expr)
            .map(|(_, value)| value)
    }
}

/// Evaluate an expression symbolically using `[[ValueSummary]]`.
/// Note that this function will not re-compute expressions if a corresponding value is already available.
pub fn eval(
    ctx: &mut ValueContext,
    gc: &mut GuardCtx,
    values: &(impl GetExprValue<ExprRef> + ?Sized),
    expr: ExprRef,
) -> ValueSummary<ExprRef> {
    // check to see if the value is already available
    if let Some(value) = values.get(expr) {
        return (*value).clone();
    }

    let mut stack = Vec::with_capacity(4);
    let mut todo: SmallVec<[(ExprRef, bool); 4]> = SmallVec::with_capacity(4);
    todo.push((expr, false));

    while let Some((e, args_available)) = todo.pop() {
        let expr = ctx[e].clone();

        // Check if there are children that we need to compute first.
        if !args_available {
            // Check to see if a value is already provided. In that case, we do not
            // need to evaluate the children, we just directly use the value.
            if let Some(value) = values.get(e) {
                stack.push((*value).clone());
                continue; // done
            }

            // otherwise, we check if there are child expressions to evaluate
            let mut has_child = false;
            expr.for_each_child(|c| {
                if !has_child {
                    has_child = true;
                    todo.push((e, true));
                }
                todo.push((*c, false));
            });
            // we need to process the children first
            if has_child {
                continue;
            }
        }

        // Otherwise, all arguments are available on the stack for us to use.
        match expr {
            // nullary
            Expr::BVSymbol { name, width } => {
                // we should not get here
                // TODO: turn into return Err
                panic!("No value found for symbol: {} : bv<{width}>", ctx[name]);
            }
            Expr::BVLiteral(_) => stack.push(ValueSummary::new(e)),
            // unary
            Expr::BVZeroExt { by, .. } => un_op(&mut stack, |e| ctx.zero_extend(e, by)),
            Expr::BVSignExt { by, .. } => un_op(&mut stack, |e| ctx.sign_extend(e, by)),
            Expr::BVSlice { hi, lo, .. } => un_op(&mut stack, |e| ctx.slice(e, hi, lo)),
            Expr::BVNot(_, _) => un_op(&mut stack, |e| ctx.not(e)),
            Expr::BVNegate(_, _) => un_op(&mut stack, |e| ctx.negate(e)),
            // binary
            // Expr::BVEqual(_, _) => bin_op(&mut stack, |a, b| a.is_equal(&b).into()),
            // Expr::BVImplies(_, _) => bin_op(&mut stack, |a, b| a.not().or(&b)),
            // Expr::BVGreater(_, _) => bin_op(&mut stack, |a, b| a.is_greater(&b).into()),
            // Expr::BVGreaterSigned(_, _, _) => {
            //     bin_op(&mut stack, |a, b| a.is_greater_signed(&b).into())
            // }
            // Expr::BVGreaterEqual(_, _) => {
            //     bin_op(&mut stack, |a, b| a.is_greater_or_equal(&b).into())
            // }
            // Expr::BVGreaterEqualSigned(_, _, _) => {
            //     bin_op(&mut stack, |a, b| a.is_greater_or_equal_signed(&b).into())
            // }
            // Expr::BVConcat(_, _, _) => bin_op(&mut stack, |a, b| a.concat(&b)),
            // // binary arithmetic
            // Expr::BVAnd(_, _, _) => bin_op(&mut stack, |a, b| a.and(&b)),
            // Expr::BVOr(_, _, _) => bin_op(&mut stack, |a, b| a.or(&b)),
            // Expr::BVXor(_, _, _) => bin_op(&mut stack, |a, b| a.xor(&b)),
            // Expr::BVShiftLeft(_, _, _) => bin_op(&mut stack, |a, b| a.shift_left(&b)),
            // Expr::BVArithmeticShiftRight(_, _, _) => {
            //     bin_op(&mut stack, |a, b| a.arithmetic_shift_right(&b))
            // }
            // Expr::BVShiftRight(_, _, _) => bin_op(&mut stack, |a, b| a.shift_right(&b)),
            Expr::BVAdd(_, _, _) => bin_op(gc, &mut stack, |a, b| ctx.add(a, b)),
            // Expr::BVMul(_, _, _) => bin_op(&mut stack, |a, b| a.mul(&b)),
            // div, rem and mod are still TODO
            Expr::BVSignedDiv(_, _, _)
            | Expr::BVUnsignedDiv(_, _, _)
            | Expr::BVSignedMod(_, _, _)
            | Expr::BVSignedRem(_, _, _)
            | Expr::BVUnsignedRem(_, _, _) => {
                todo!("implement eval support for {:?}", ctx[e])
            }
            // Expr::BVSub(_, _, _) => bin_op(&mut stack, |a, b| a.sub(&b)),
            // BVArrayRead needs array support!
            Expr::BVIte { .. } => {
                // TODO: calculate cond first and then selectively compute tru and fals depending on result

                let cond = stack.pop().unwrap();
                let tru = stack.pop().unwrap();
                let fals = stack.pop().unwrap();
                let res = ValueSummary::apply_ite(ctx, gc, cond, tru, fals);
                stack.push(res);
            }
            // array ops
            // Expr::BVArrayRead { .. } => {
            //     let array = array_stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("array argument is missing"));
            //     let index = stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("index argument is missing"));
            //     stack.push(array.select(&index));
            // }
            // Expr::ArraySymbol {
            //     name,
            //     index_width,
            //     data_width,
            // } => {
            //     // we should not get here
            //     // TODO: turn into return Err
            //     panic!(
            //         "No value found for symbol: {} : bv<{index_width}> -> bv<{data_width}>",
            //         ctx[*name]
            //     );
            // }
            // Expr::ArrayConstant { index_width, .. } => {
            //     let default = stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("default (e) argument is missing"));
            //     array_stack.push(ArrayValue::new_sparse(*index_width, &default));
            // }
            // Expr::ArrayEqual(_, _) => {
            //     let a = array_stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("array a argument is missing"));
            //     let b = array_stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("array b argument is missing"));
            //     stack.push(a.is_equal(&b).unwrap_or_default().into())
            // }
            // Expr::ArrayStore { .. } => {
            //     let array = array_stack
            //         .last_mut()
            //         .unwrap_or_else(|| panic!("array argument is missing"));
            //     let index = stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("index argument is missing"));
            //     let data = stack
            //         .pop()
            //         .unwrap_or_else(|| panic!("data argument is missing"));
            //     array.store(&index, &data); // we avoid pop + push by modifying in place
            // }
            // Expr::ArrayIte { .. } => {
            //     let cond = stack.pop().unwrap().to_bool().unwrap();
            //     if cond {
            //         let tru = array_stack.pop().unwrap();
            //         array_stack.pop().unwrap();
            //         array_stack.push(tru);
            //     } else {
            //         array_stack.pop().unwrap(); // just discard tru
            //     }
            // }
            other => todo!("add support for {other:?}"),
        }
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

#[inline]
fn un_op(stack: &mut Vec<ValueSummary<ExprRef>>, mut op: impl FnMut(ExprRef) -> ExprRef) {
    let e = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let res = e.apply_un_op(&mut op);
    stack.push(res);
}

#[inline]
fn bin_op(
    gc: &mut GuardCtx,
    stack: &mut Vec<ValueSummary<ExprRef>>,
    mut op: impl FnMut(ExprRef, ExprRef) -> ExprRef,
) {
    let a = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let b = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let res = ValueSummary::apply_bin_op(gc, &mut op, a, b);
    stack.push(res);
}

#[cfg(test)]
mod tests {
    use super::*;
    use patronus::expr::{Context, SerializableIrNode};
    use smallvec::smallvec;

    #[test]
    fn simple_eval() {
        let mut ctx = Context::default();
        let mut gc = GuardCtx::default();

        let reset = ctx.bv_symbol("reset", 1);
        let inp = ctx.bv_symbol("inp", 32);
        let out = ctx.build(|c| c.ite(reset, c.zero(32), c.add(inp, c.one(32))));

        let symbols = [(reset, ctx.get_false().into()), (inp, inp.into())];
        let result = eval(&mut ctx, &mut gc, symbols.as_slice(), out);
        println!("Entries: {}", result.len());
        println!("In: {}", out.serialize_to_str(&ctx));
        println!(
            "Out: {}",
            result.to_value(&mut ctx, &mut gc).serialize_to_str(&ctx)
        )
    }
}
