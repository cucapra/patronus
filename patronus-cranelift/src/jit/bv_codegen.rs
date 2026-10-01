// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>

use baa::{BitVecOps, BitVecValueRef};
use cranelift::prelude::*;
use patronus::expr::*;

macro_rules! iconst {
    ($ctx: expr, $value: expr) => {
        $ctx.fn_builder.ins().iconst(INT_T, ($value) as i64)
    };
}
pub(super) use iconst;

/// Given width of a bit vec value, select the smallest primitive type that is able to represent it
pub(super) fn select_container_primitive(width: WidthInt) -> cranelift::prelude::Type {
    match width {
        1..=8 => types::I8,
        9..=16 => types::I16,
        17..=32 => types::I32,
        33..=64 => types::I64,
        _ => panic!("unsupported width for thin bit vec"),
    }
}

// ensuring bitwidth correctness
// - all inputs to codegen are of correct bitwidth
// - all generated code will preserve correct bitwidth
// - so, comparisons do not have to pad to bitwidth
// also assuming that the frontend will check for invalid expressions

// TODO: check if the signed ge / lt work

/// Unsigned extend input `value` to fit target width.
pub(super) fn extend_to_fit(
    b: &mut FunctionBuilder,
    value: Value,
    src_width: WidthInt,
    dest_width: WidthInt,
) -> Value {
    let prev_type = select_container_primitive(src_width);
    let target_type = select_container_primitive(dest_width);
    if !prev_type.eq(&target_type) {
        b.ins().uextend(target_type, value)
    } else {
        value
    }
}

fn mask(b: &mut FunctionBuilder, value: Value, width: WidthInt) -> Value {
    if width < 64 {
        b.ins().band_imm(value, ((u64::MAX) >> (64 - width)) as i64)
    } else {
        value
    }
}

pub fn literal(b: &mut FunctionBuilder, value: BitVecValueRef, width: WidthInt) -> Value {
    b.ins().iconst(
        select_container_primitive(width),
        value.to_u64().unwrap() as i64,
    )
}

pub fn add(b: &mut FunctionBuilder, lhs: Value, rhs: Value, width: WidthInt) -> Value {
    let v1 = b.ins().iadd(lhs, rhs);
    mask(b, v1, width)
}
pub fn sub(b: &mut FunctionBuilder, lhs: Value, rhs: Value, width: WidthInt) -> Value {
    let v1 = b.ins().isub(lhs, rhs);
    mask(b, v1, width)
}
pub fn mul(b: &mut FunctionBuilder, lhs: Value, rhs: Value, width: WidthInt) -> Value {
    let v1 = b.ins().imul(lhs, rhs);
    mask(b, v1, width)
}

pub fn not(b: &mut FunctionBuilder, arg: Value, width: WidthInt) -> Value {
    let tmp = b.ins().bnot(arg);
    mask(b, tmp, width)
}
pub fn negate(b: &mut FunctionBuilder, arg: Value, width: WidthInt) -> Value {
    let flipped = b.ins().bnot(arg);
    let tmp = b.ins().iadd_imm(flipped, 1);
    mask(b, tmp, width)
}

pub fn zero_extend(b: &mut FunctionBuilder, arg: Value, by: WidthInt, width: WidthInt) -> Value {
    extend_to_fit(b, arg, width, width + by)
}
pub fn sign_extend(b: &mut FunctionBuilder, arg: Value, by: WidthInt, width: WidthInt) -> Value {
    let mut ret = extend_to_fit(b, arg, width, width + by);
    let num_leading_zeros = select_container_primitive(by + width).bytes() * 8 - width;
    if num_leading_zeros != 0 {
        let shifted = b.ins().ishl_imm(ret, num_leading_zeros as i64);
        ret = b.ins().sshr_imm(shifted, num_leading_zeros as i64);
    }
    mask(b, ret, width + by)
}

pub fn shift_right(b: &mut FunctionBuilder, arg0: Value, arg1: Value, width: WidthInt) -> Value {
    let v1 = b.ins().ushr(arg0, arg1);
    mask(b, v1, width)
}
pub fn arithmetic_shift_right(
    b: &mut FunctionBuilder,
    arg0: Value,
    arg1: Value,
    width: WidthInt,
) -> Value {
    let v1 = b.ins().sshr(arg0, arg1);
    mask(b, v1, width)
}
pub fn shift_left(b: &mut FunctionBuilder, arg0: Value, arg1: Value, width: WidthInt) -> Value {
    let v1 = b.ins().ishl(arg0, arg1);
    mask(b, v1, width)
}

pub fn concat(
    b: &mut FunctionBuilder,
    hi: Value,
    hi_width: WidthInt,
    lo: Value,
    lo_width: WidthInt,
) -> Value {
    let tot_width = hi_width + lo_width;
    let (hi, lo) = (
        extend_to_fit(b, hi, hi_width, tot_width),
        extend_to_fit(b, lo, lo_width, tot_width),
    );
    let hi = b.ins().ishl_imm(hi, lo_width as i64);
    b.ins().bor(hi, lo)
}

pub fn slice(b: &mut FunctionBuilder, value: Value, hi: WidthInt, lo: WidthInt) -> Value {
    let shifted = b.ins().ushr_imm(value, lo as i64);
    mask(b, shifted, hi - lo + 1)
}
pub fn implies(b: &mut FunctionBuilder, lhs: Value, rhs: Value, width: WidthInt) -> Value {
    let lhs = b.ins().bnot(lhs);
    let ret = b.ins().bor(lhs, rhs);
    mask(b, ret, width)
}
