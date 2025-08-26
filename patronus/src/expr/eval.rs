// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::{Context, Expr, ExprRef, ForEachChild, TypeCheck};
use baa::{
    ArrayMutOps, ArrayOps, ArrayValue, BitVecMutOps, BitVecOps, BitVecValue, BitVecValueIndex,
    BitVecValueRef, IndexToMutRef, IndexToRef, Value, Word,
};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::collections::HashMap;

/// Returns a value for an expression if it is available.
pub trait GetExprValue {
    fn get_bv(&self, ctx: &Context, symbol: ExprRef) -> Option<BitVecValue>;
    fn get_array(&self, ctx: &Context, symbol: ExprRef) -> Option<ArrayValue>;
}

type SymbolValueStoreIndex = u32;

#[derive(Default, Clone)]
pub struct SymbolValueStore {
    arrays: Vec<ArrayValue>,
    bit_vec_words: Vec<Word>,
    lookup: FxHashMap<ExprRef, SymbolValueStoreIndex>,
}

impl SymbolValueStore {
    pub fn define_bv<'a>(&mut self, symbol: ExprRef, value: impl Into<BitVecValueRef<'a>>) {
        let value = value.into();
        let index = self.bit_vec_words.len() as SymbolValueStoreIndex;
        debug_assert!(!self.lookup.contains_key(&symbol));
        self.lookup.insert(symbol, index);
        self.bit_vec_words.extend_from_slice(value.words());
    }

    pub fn update_bv<'a>(&mut self, symbol: ExprRef, value: impl Into<BitVecValueRef<'a>>) {
        let value = value.into();
        let raw_index = self.lookup[&symbol];
        let index = BitVecValueIndex::new(raw_index, value.width());
        self.bit_vec_words.get_mut_ref(index).assign(value);
    }

    pub fn define_array(&mut self, symbol: ExprRef, value: ArrayValue) {
        let index = self.arrays.len() as SymbolValueStoreIndex;
        debug_assert!(!self.lookup.contains_key(&symbol));
        self.lookup.insert(symbol, index);
        self.arrays.push(value);
    }

    pub fn update_array(&mut self, symbol: ExprRef, value: ArrayValue) {
        let raw_index = self.lookup[&symbol];
        self.arrays[raw_index as usize] = value;
    }

    pub fn update(&mut self, symbol: ExprRef, value: Value) {
        match value {
            Value::Array(value) => self.update_array(symbol, value),
            Value::BitVec(value) => self.update_bv(symbol, &value),
        }
    }

    pub fn clear(&mut self) {
        self.arrays.clear();
        self.bit_vec_words.clear();
        self.lookup.clear();
    }
}

impl GetExprValue for SymbolValueStore {
    fn get_bv(&self, ctx: &Context, symbol: ExprRef) -> Option<BitVecValue> {
        let width = symbol.get_bv_type(ctx)?;
        let index = BitVecValueIndex::new(*self.lookup.get(&symbol)?, width);
        Some(self.bit_vec_words.get_ref(index).into())
    }

    #[cfg(debug_assertions)]
    fn get_array(&self, ctx: &Context, symbol: ExprRef) -> Option<ArrayValue> {
        let tpe = symbol.get_array_type(ctx).unwrap();
        let value = self.arrays[*self.lookup.get(&symbol)? as usize].clone();
        debug_assert_eq!(value.data_width(), tpe.data_width);
        debug_assert_eq!(value.index_width(), tpe.index_width);
        Some(value)
    }

    #[cfg(not(debug_assertions))]
    fn get_array(&self, _ctx: &Context, symbol: ExprRef) -> Option<ArrayValue> {
        Some(self.arrays[*self.lookup.get(&symbol)? as usize].clone())
    }
}

impl From<&[(ExprRef, BitVecValue)]> for SymbolValueStore {
    fn from(value: &[(ExprRef, BitVecValue)]) -> Self {
        let mut out = SymbolValueStore::default();
        for (expr, value) in value.iter() {
            out.define_bv(*expr, value);
        }
        out
    }
}

impl From<&[(ExprRef, ArrayValue)]> for SymbolValueStore {
    fn from(value: &[(ExprRef, ArrayValue)]) -> Self {
        let mut out = SymbolValueStore::default();
        for (expr, value) in value.iter() {
            out.define_array(*expr, value.clone());
        }
        out
    }
}

impl GetExprValue for HashMap<ExprRef, BitVecValue> {
    fn get_bv(&self, _ctx: &Context, symbol: ExprRef) -> Option<BitVecValue> {
        self.get(&symbol).cloned()
    }

    fn get_array(&self, _ctx: &Context, _symbol: ExprRef) -> Option<ArrayValue> {
        None
    }
}

impl GetExprValue for [(ExprRef, BitVecValue)] {
    fn get_bv(&self, _ctx: &Context, symbol: ExprRef) -> Option<BitVecValue> {
        self.iter()
            .find(|(e, _v)| *e == symbol)
            .map(|(_e, v)| v.clone())
    }

    fn get_array(&self, _ctx: &Context, _symbol: ExprRef) -> Option<ArrayValue> {
        None
    }
}

impl GetExprValue for [(ExprRef, ArrayValue)] {
    fn get_bv(&self, _ctx: &Context, _symbol: ExprRef) -> Option<BitVecValue> {
        None
    }

    fn get_array(&self, _ctx: &Context, symbol: ExprRef) -> Option<ArrayValue> {
        self.iter()
            .find(|(e, _v)| *e == symbol)
            .map(|(_e, v)| v.clone())
    }
}

type BitVecStack = SmallVec<[BitVecValue; 4]>;
type ArrayStack = SmallVec<[ArrayValue; 2]>;

#[inline]
fn un_op(stack: &mut BitVecStack, op: impl Fn(BitVecValue) -> BitVecValue) {
    let e = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let res = op(e);
    stack.push(res);
}

#[inline]
fn bin_op(stack: &mut BitVecStack, op: impl Fn(BitVecValue, BitVecValue) -> BitVecValue) {
    let a = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let b = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let res = op(a, b);
    stack.push(res);
}

pub fn eval_bv_expr(
    ctx: &Context,
    symbols: &(impl GetExprValue + ?Sized),
    expr: ExprRef,
) -> BitVecValue {
    debug_assert!(
        ctx[expr].get_bv_type(ctx).is_some(),
        "Not a bit-vector expression: {:?}",
        ctx[expr]
    );
    let (mut bv_stack, array_stack) = eval_expr_internal(ctx, symbols, expr);
    debug_assert!(array_stack.is_empty());
    debug_assert_eq!(bv_stack.len(), 1);
    bv_stack.pop().unwrap()
}

pub fn eval_array_expr(
    ctx: &Context,
    symbols: &(impl GetExprValue + ?Sized),
    expr: ExprRef,
) -> ArrayValue {
    debug_assert!(
        ctx[expr].get_array_type(ctx).is_some(),
        "Not an array expression: {:?}",
        ctx[expr]
    );
    let (bv_stack, mut array_stack) = eval_expr_internal(ctx, symbols, expr);
    debug_assert!(bv_stack.is_empty());
    debug_assert_eq!(array_stack.len(), 1);
    array_stack.pop().unwrap()
}

pub fn eval_expr(ctx: &Context, symbols: &(impl GetExprValue + ?Sized), expr: ExprRef) -> Value {
    let (mut bv_stack, mut array_stack) = eval_expr_internal(ctx, symbols, expr);
    debug_assert_eq!(bv_stack.len() + array_stack.len(), 1);
    if let Some(value) = bv_stack.pop() {
        debug_assert!(ctx[expr].is_bv_type());
        Value::BitVec(value)
    } else {
        let value = array_stack.pop().unwrap();
        debug_assert!(ctx[expr].is_array_type());
        Value::Array(value)
    }
}

fn eval_expr_internal(
    ctx: &Context,
    values: &(impl GetExprValue + ?Sized),
    expr: ExprRef,
) -> (BitVecStack, ArrayStack) {
    let mut bv_stack: BitVecStack = SmallVec::with_capacity(4);
    let mut array_stack: ArrayStack = SmallVec::with_capacity(2);
    let mut todo: SmallVec<[(ExprRef, bool); 4]> = SmallVec::with_capacity(4);

    todo.push((expr, false));
    while let Some((e, args_available)) = todo.pop() {
        let expr = &ctx[e];

        // Check if there are children that we need to compute first.
        if !args_available {
            // Check to see if a value is already provided. In that case, we do not
            // need to evaluate the children, we just directly use the value.
            if expr.is_bv_type() {
                if let Some(value) = values.get_bv(ctx, e) {
                    bv_stack.push(value);
                    continue; // done
                }
            } else {
                debug_assert!(expr.is_array_type());
                if let Some(value) = values.get_array(ctx, e) {
                    array_stack.push(value);
                    continue; // done
                }
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
                panic!("No value found for symbol: {} : bv<{width}>", ctx[*name]);
            }
            Expr::BVLiteral(value) => bv_stack.push(value.get(ctx).into()),
            // unary
            Expr::BVZeroExt { by, .. } => un_op(&mut bv_stack, |e| e.zero_extend(*by)),
            Expr::BVSignExt { by, .. } => un_op(&mut bv_stack, |e| e.sign_extend(*by)),
            Expr::BVSlice { hi, lo, .. } => un_op(&mut bv_stack, |e| e.slice(*hi, *lo)),
            Expr::BVNot(_, _) => un_op(&mut bv_stack, |e| e.not()),
            Expr::BVNegate(_, _) => un_op(&mut bv_stack, |e| e.negate()),
            // binary
            Expr::BVEqual(_, _) => bin_op(&mut bv_stack, |a, b| a.is_equal(&b).into()),
            Expr::BVImplies(_, _) => bin_op(&mut bv_stack, |a, b| a.not().or(&b)),
            Expr::BVGreater(_, _) => bin_op(&mut bv_stack, |a, b| a.is_greater(&b).into()),
            Expr::BVGreaterSigned(_, _, _) => {
                bin_op(&mut bv_stack, |a, b| a.is_greater_signed(&b).into())
            }
            Expr::BVGreaterEqual(_, _) => {
                bin_op(&mut bv_stack, |a, b| a.is_greater_or_equal(&b).into())
            }
            Expr::BVGreaterEqualSigned(_, _, _) => bin_op(&mut bv_stack, |a, b| {
                a.is_greater_or_equal_signed(&b).into()
            }),
            Expr::BVConcat(_, _, _) => bin_op(&mut bv_stack, |a, b| a.concat(&b)),
            // binary arithmetic
            Expr::BVAnd(_, _, _) => bin_op(&mut bv_stack, |a, b| a.and(&b)),
            Expr::BVOr(_, _, _) => bin_op(&mut bv_stack, |a, b| a.or(&b)),
            Expr::BVXor(_, _, _) => bin_op(&mut bv_stack, |a, b| a.xor(&b)),
            Expr::BVShiftLeft(_, _, _) => bin_op(&mut bv_stack, |a, b| a.shift_left(&b)),
            Expr::BVArithmeticShiftRight(_, _, _) => {
                bin_op(&mut bv_stack, |a, b| a.arithmetic_shift_right(&b))
            }
            Expr::BVShiftRight(_, _, _) => bin_op(&mut bv_stack, |a, b| a.shift_right(&b)),
            Expr::BVAdd(_, _, _) => bin_op(&mut bv_stack, |a, b| a.add(&b)),
            Expr::BVMul(_, _, _) => bin_op(&mut bv_stack, |a, b| a.mul(&b)),
            // div, rem and mod are still TODO
            Expr::BVSignedDiv(_, _, _)
            | Expr::BVUnsignedDiv(_, _, _)
            | Expr::BVSignedMod(_, _, _)
            | Expr::BVSignedRem(_, _, _)
            | Expr::BVUnsignedRem(_, _, _) => {
                todo!("implement eval support for {:?}", ctx[e])
            }
            Expr::BVSub(_, _, _) => bin_op(&mut bv_stack, |a, b| a.sub(&b)),
            // BVArrayRead needs array support!
            Expr::BVIte { .. } => {
                let cond = bv_stack.pop().unwrap().to_bool().unwrap();
                if cond {
                    let tru = bv_stack.pop().unwrap();
                    bv_stack.pop().unwrap();
                    bv_stack.push(tru);
                } else {
                    bv_stack.pop().unwrap(); // just discard tru
                }
            }
            // array ops
            Expr::BVArrayRead { .. } => {
                let array = array_stack
                    .pop()
                    .unwrap_or_else(|| panic!("array argument is missing"));
                let index = bv_stack
                    .pop()
                    .unwrap_or_else(|| panic!("index argument is missing"));
                bv_stack.push(array.select(&index));
            }
            Expr::ArraySymbol {
                name,
                index_width,
                data_width,
            } => {
                // we should not get here
                // TODO: turn into return Err
                panic!(
                    "No value found for symbol: {} : bv<{index_width}> -> bv<{data_width}>",
                    ctx[*name]
                );
            }
            Expr::ArrayConstant { index_width, .. } => {
                let default = bv_stack
                    .pop()
                    .unwrap_or_else(|| panic!("default (e) argument is missing"));
                array_stack.push(ArrayValue::new_sparse(*index_width, &default));
            }
            Expr::ArrayEqual(_, _) => {
                let a = array_stack
                    .pop()
                    .unwrap_or_else(|| panic!("array a argument is missing"));
                let b = array_stack
                    .pop()
                    .unwrap_or_else(|| panic!("array b argument is missing"));
                bv_stack.push(a.is_equal(&b).unwrap_or_default().into())
            }
            Expr::ArrayStore { .. } => {
                let array = array_stack
                    .last_mut()
                    .unwrap_or_else(|| panic!("array argument is missing"));
                let index = bv_stack
                    .pop()
                    .unwrap_or_else(|| panic!("index argument is missing"));
                let data = bv_stack
                    .pop()
                    .unwrap_or_else(|| panic!("data argument is missing"));
                array.store(&index, &data); // we avoid pop + push by modifying in place
            }
            Expr::ArrayIte { .. } => {
                let cond = bv_stack.pop().unwrap().to_bool().unwrap();
                if cond {
                    let tru = array_stack.pop().unwrap();
                    array_stack.pop().unwrap();
                    array_stack.push(tru);
                } else {
                    array_stack.pop().unwrap(); // just discard tru
                }
            }
        }
    }

    debug_assert_eq!(bv_stack.len() + array_stack.len(), 1);
    (bv_stack, array_stack)
}

#[cfg(test)]
mod tests {
    use super::{SymbolValueStore, eval_array_expr, eval_bv_expr};
    use crate::expr::*;
    use baa::*;

    #[test]
    fn test_eval_bv_expr() {
        let mut c = Context::default();

        // boolean
        let a = c.bv_symbol("a", 1);
        let a_and_1 = c.build(|c| c.and(a, c.one(1)));
        assert!(eval_bv_expr(&c, [(a, BitVecValue::new_true())].as_slice(), a_and_1).is_true());
        assert!(eval_bv_expr(&c, [(a, BitVecValue::new_false())].as_slice(), a_and_1).is_false());
        let b = c.bv_symbol("b", 1);
        let expr = c.build(|c| c.or(c.and(a, c.not(b)), c.and(a, b)));
        assert!(
            eval_bv_expr(
                &c,
                [(a, BitVecValue::new_false()), (b, BitVecValue::new_false())].as_slice(),
                expr
            )
            .is_false()
        );

        // arithmetic and ite
        let a = c.bv_symbol("a", 128);
        let b = c.bv_symbol("b", 128);
        let expr = c.build(|c| {
            c.ite(
                c.greater_signed(a, c.bv_lit(&BitVecValue::from_u64(0, 128))),
                c.sub(b, a),
                c.add(b, a),
            )
        });
        {
            let eval = |a_v: i64, b_v: i64| -> i64 {
                let symbols = [
                    (a, BitVecValue::from_i64(a_v, 128)),
                    (b, BitVecValue::from_i64(b_v, 128)),
                ];
                let res = eval_bv_expr(&c, symbols.as_slice(), expr);
                res.to_i64().unwrap()
            };
            assert_eq!(eval(1, 0), -1);
            assert_eq!(eval(-1, 0), -1);
            assert_eq!(eval(-1, -2), -3);
            assert_eq!(eval(-1, 2000), 2000 - 1);
            assert_eq!(eval(1000, 2000), 2000 - 1000);
        }
    }

    #[test]
    fn test_eval_bv_expr_with_array_expr() {
        let mut c = Context::default();
        let a = c.array_symbol("a", 4, 32);
        let mut a_values = ArrayValue::new_sparse(4, &BitVecValue::zero(64));
        for ii in 0..(1 << 4) {
            let ii_squared = BitVecValue::from_u64(ii * ii, 64);
            a_values.store(&BitVecValue::from_u64(ii, 4), &ii_squared);
        }

        // read from constant address
        for ii in 0..(1 << 4) {
            let read_ii = c.build(|c| c.array_read(a, c.bv_lit(&BitVecValue::from_u64(ii, 4))));
            let value_at_ii = eval_bv_expr(&c, [(a, a_values.clone())].as_slice(), read_ii)
                .to_u64()
                .unwrap();
            assert_eq!(value_at_ii, ii * ii);
        }
    }

    #[test]
    fn test_eval_array_expr() {
        let mut c = Context::default();
        let const_123_array = c.build(|c| c.array_const(c.bv_lit(&BitVecValue::zero(64)), 4));
        for ii in 0..(1 << 4) {
            let addr = BitVecValue::from_u64(ii, 4);
            let value = BitVecValue::from_u64(ii * ii * ii, 64);
            let expr =
                c.build(|c| c.array_store(const_123_array, c.bv_lit(&addr), c.bv_lit(&value)));
            let res = eval_array_expr(&c, &SymbolValueStore::default(), expr);
            // check result
            for jj in 0..(1 << 4) {
                let value = res.select(&BitVecValue::from_u64(jj, 4)).to_u64().unwrap();
                if jj == ii {
                    assert_eq!(value, jj * jj * jj);
                } else {
                    assert_eq!(value, 0);
                }
            }
        }
    }
}
