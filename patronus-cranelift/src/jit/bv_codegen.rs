// Copyright 2025-2026 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
// author: Willow Ge <lg634@cornell.edu>

use baa::{BitVecOps, BitVecValueRef};
use cranelift::prelude::*;
use patronus::expr::*;

use cranelift::codegen::ir as clir;

/// Given width of a bit vec value, select the smallest primitive type that is able to represent it
pub(super) fn select_contain_t(width: WidthInt) -> cranelift::prelude::Type {
    match width {
        1..=8 => types::I8,
        9..=16 => types::I16,
        17..=32 => types::I32,
        33..=64 => types::I64,
        // _ => make_vect(width),
        _ => panic!("unsupported width for thin bit vec"),
    }
}

// ensuring bitwidth correctness
// - all inputs to codegen are of correct bitwidth
// - all generated code will preserve correct bitwidth
// - so, comparisons do not have to pad to bitwidth
// also assuming that the frontend will check for invalid expressions

// TODO: check if the signed ge / lt work

// lakeroad is a reasonable test
// 16378 as highest in the 1GB design

/// Unsigned extend input `value` to fit target width.
pub(super) fn extend_to_fit(
    b: &mut FunctionBuilder,
    value: Value,
    src_width: WidthInt,
    dest_width: WidthInt,
) -> Value {
    let prev_t = select_contain_t(src_width);
    let target_t = select_contain_t(dest_width);
    if prev_t == target_t {
        return value;
    }

    // case: input int, output int
    b.ins().uextend(target_t, value)
}

// value should map to the same type as the widthint
fn mask(b: &mut FunctionBuilder, value: Value, width: WidthInt) -> Value {
    // case: mask an int
    if width == 64 {
        return value;
    } else if width < 64 {
        b.ins()
            .band_imm_u(value, ((u64::MAX) >> (64 - width)) as i64)
    } else {
        panic!()
    }
}

pub fn literal(b: &mut FunctionBuilder, value: BitVecValueRef, width: WidthInt) -> Value {
    let target_t = select_contain_t(width);

    // case: int
    b.ins().iconst(target_t, value.to_u64().unwrap() as i64)
}

pub fn concat(
    b: &mut FunctionBuilder,
    hi: Value,
    hi_width: WidthInt,
    lo: Value,
    lo_width: WidthInt,
) -> Value {
    // case: two int, output int
    let tot_width = hi_width + lo_width;
    let (hi, lo) = if lo_width < 64 {
        let (hi, lo) = (
            extend_to_fit(b, hi, hi_width, tot_width),
            extend_to_fit(b, lo, lo_width, tot_width),
        );
        // shifts on vectors essentially apply the shift operation to each lane, with no overflow from lane to lane. so, this thing
        let hi = b.ins().ishl_imm_u(hi, lo_width as i64);
        (hi, lo)
    } else {
        let lane_idx = lo_width / 64;
        let lo = extend_to_fit(b, lo, lo_width, tot_width);
        let hi = extend_to_fit(b, hi, hi_width, 64);
        let hi = b.ins().ishl_imm_u(hi, (lo_width % 64) as i64);
        // println!("{:?}", hi);

        // create a zeroed vector
        let container = select_contain_t(tot_width);
        let zeroed = b.ins().iconst(types::I64, 0);
        let mut out_v = b.ins().splat(container, zeroed);
        out_v = b.ins().insertlane(out_v, hi, lane_idx as u8);
        (out_v, lo)
    };
    b.ins().bor(hi, lo)
}

pub fn slice(
    b: &mut FunctionBuilder,
    value: Value,
    hi: WidthInt,
    lo: WidthInt,
    tot_width: WidthInt,
) -> Value {
    // TODO: this is almost certainly broken

    let orig_t = select_contain_t(tot_width);
    let new_t = select_contain_t(hi - lo + 1);

    let shifted = b.ins().ushr_imm_u(value, lo as i64);
    // case: slice int to int
    let tmp = mask(b, shifted, hi - lo + 1);
    if !orig_t.eq(&new_t) {
        b.ins().ireduce(new_t, tmp)
    } else {
        tmp // no need to reduce
    }
}

pub fn zero_extend(b: &mut FunctionBuilder, arg: Value, by: WidthInt, width: WidthInt) -> Value {
    extend_to_fit(b, arg, width - by, width)
}
pub fn sign_extend(b: &mut FunctionBuilder, arg: Value, by: WidthInt, width: WidthInt) -> Value {
    let mut ret = extend_to_fit(b, arg, width - by, width);

    // TODO: this is borked for wide bitvecs
    let num_leading_zeros = select_contain_t(width % 64).bytes() * 8 - (width % 64);
    if num_leading_zeros != 0 {
        let shifted = b.ins().ishl_imm_u(ret, num_leading_zeros as i64);

        ret = b.ins().sshr_imm_u(shifted, num_leading_zeros as i64);
    }
    mask(b, ret, width)
}

// NOTE: the following are non-functional on wide bitvectors
// begin:

// value should map to the same type as the widthint
fn mask_scalar(b: &mut FunctionBuilder, value: Value, width: WidthInt) -> Value {
    // case: mask an int
    if width == 64 {
        return value;
    } else if width < 64 {
        b.ins()
            .band_imm_u(value, ((u64::MAX) >> (64 - width)) as i64)
    } else {
        panic!()
    }
}

// build an operation which requires a masking at the end
pub fn build_fixedw_op(
    b: &mut FunctionBuilder,
    op: clir::Opcode,
    arg0: Value,
    arg1: Value,
    out_width: WidthInt,
) -> Value {
    // let op_t = op.format();
    // TODO: might be helpful to assert that it is binary

    let (r, dfg) = b.ins().Binary(op, select_contain_t(out_width), arg0, arg1);
    let bin_ov = dfg.inst_results(r)[0];
    mask_scalar(b, bin_ov, out_width)
}

pub fn not(b: &mut FunctionBuilder, arg: Value, width: WidthInt) -> Value {
    let tmp = b.ins().bnot(arg);
    mask(b, tmp, width)
}
pub fn negate(b: &mut FunctionBuilder, arg: Value, width: WidthInt) -> Value {
    let flipped = b.ins().bnot(arg);
    let tmp = b.ins().iadd_imm_u(flipped, 1);
    mask(b, tmp, width)
}

pub fn implies(b: &mut FunctionBuilder, lhs: Value, rhs: Value, width: WidthInt) -> Value {
    let lhs = b.ins().bnot(lhs);
    let ret = b.ins().bor(lhs, rhs);
    mask(b, ret, width)
}

// end
