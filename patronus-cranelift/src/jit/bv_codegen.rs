// Copyright 2025-2026 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
// author: Willow Ge <lg634@cornell.edu>

use baa::{BitVecOps, BitVecValueRef};
use cranelift::prelude::*;
use patronus::expr::*;

/// Given width of a bit vec value, select the smallest primitive type that is able to represent it
pub(super) fn select_container_primitive(width: WidthInt) -> cranelift::prelude::Type {
    match width {
        1..=8 => types::I8,
        9..=16 => types::I16,
        17..=32 => types::I32,
        33..=64 => types::I64,
        _ => make_vect(width),
        // _ => panic!("unsupported width for thin bit vec"),
    }
}

fn make_vect(width: WidthInt) -> cranelift::prelude::Type {
    let lane_ct = crate::jit::slot_new::calc_words::<64>(width);
    types::I64.by(lane_ct as u32).unwrap()
}

// ensuring bitwidth correctness
// - all inputs to codegen are of correct bitwidth
// - all generated code will preserve correct bitwidth
// - so, comparisons do not have to pad to bitwidth
// also assuming that the frontend will check for invalid expressions

// TODO: check if the signed ge / lt work

// tools:
// scalar_to_vector
// splat
// vconst
// insertlane, extractlane

// lakeroad is a reasonable test
// 16378 as highest in the 1GB design

/// creates a zero-initialised vector.
/// so far, this method seems to be the only one guaranteed to work
#[inline(always)]
fn zerovec(b: &mut FunctionBuilder, ty: cranelift::prelude::Type) -> Value {
    let zeroed = b.ins().iconst(types::I64, 0);
    b.ins().splat(ty, zeroed)
}

/// Unsigned extend input `value` to fit target width.
pub(super) fn extend_to_fit(
    b: &mut FunctionBuilder,
    value: Value,
    src_width: WidthInt,
    dest_width: WidthInt,
) -> Value {
    let prev_t = select_container_primitive(src_width);
    let target_t = select_container_primitive(dest_width);
    if prev_t == target_t {
        return value;
    }

    if prev_t.is_vector() && target_t.is_vector() {
        // case: input vec, output vec
        // create a zero
        // add lane(s) until complete
        let mut out_v = zerovec(b, target_t);
        for i in 0..prev_t.lane_count() {
            let old_v = b.ins().extractlane(value, i as u8);
            out_v = b.ins().insertlane(out_v, old_v, i as u8);
        }
        out_v
    } else if target_t.is_vector() {
        // case: input int, output vec
        // use scalar_to_vector / insertlane
        let source_i = if !prev_t.eq(&types::I64) {
            b.ins().uextend(types::I64, value)
        } else {
            value
        };
        b.ins().scalar_to_vector(target_t, source_i)
    } else {
        // case: input int, output int

        b.ins().uextend(target_t, value)
    }
}

// value should map to the same type as the widthint
fn mask(b: &mut FunctionBuilder, value: Value, width: WidthInt) -> Value {
    // case: mask an int
    if width == 64 {
        return value;
    } else if width < 64 {
        b.ins().band_imm(value, ((u64::MAX) >> (64 - width)) as i64)
    } else {
        // case: mask a vector
        // only the high word needs masking
        let top_bits = width % 64;
        let max_idx = (width) / 64;
        let old_v = b.ins().extractlane(value, max_idx as u8);
        let tmp = b
            .ins()
            .band_imm(old_v, ((u64::MAX) >> (64 - top_bits)) as i64);
        b.ins().insertlane(value, tmp, max_idx as u8)
    }
}

pub fn literal(b: &mut FunctionBuilder, value: BitVecValueRef, width: WidthInt) -> Value {
    let target_t = select_container_primitive(width);
    if target_t.is_vector() {
        // case: vector
        // TODO: might be good to specialise these and/or always handle them through rust
        // TODO: directly load from the ref??
        // for now, just do the very dumb thing and insert lanes
        let mut out_v = zerovec(b, target_t);
        for (idx, word) in value.words().iter().enumerate() {
            let lane_v = b.ins().iconst(types::I64, *word as i64);
            out_v = b.ins().insertlane(out_v, lane_v, idx as u8);
        }
        out_v
    } else {
        // case: int
        b.ins().iconst(target_t, value.to_u64().unwrap() as i64)
    }
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
        let hi = b.ins().ishl_imm(hi, lo_width as i64);
        (hi, lo)
    } else {
        let lane_idx = lo_width / 64;
        let lo = extend_to_fit(b, lo, lo_width, tot_width);
        let hi = b.ins().ishl_imm(hi, (lo_width % 64) as i64);

        // create a zeroed vector
        let container = select_container_primitive(tot_width);
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
    let shifted = b.ins().ushr_imm(value, lo as i64);

    let orig_t = select_container_primitive(tot_width);
    let new_t = select_container_primitive(hi - lo + 1);

    if orig_t.is_vector() {
        // on vectors, determining tmp has to be a little more nuanced: varies based on whether the output is a vector or not

        // compute which lanes the slice spans
        let lane_lo = lo / 64;
        let lane_hi = hi / 64;

        // case: selection within a single lane
        if lane_lo == lane_hi {
            // extract lane, then reduce to correct type
            let extracted_ln = b.ins().extractlane(value, (lo / 64) as u8);
            let extracted_ln = b.ins().ushr_imm(extracted_ln, lo as i64);
            if !new_t.eq(&types::I64) {
                return b.ins().ireduce(new_t, extracted_ln);
            } else {
                return extracted_ln;
            }
        }

        // right rotate every lane by `lo`
        // let rot_l = b.ins().rotr_imm_u(value, lo as i64);

        // given N lanes:
        // - laneno < N-1: laneno+1's upper `lo` bits will contain the value that needs to be 'carried' over to the upper `lo` bits of the current lane
        // - laneno == N-1: uppermost lane. zeroes are carried in.

        // upper `lo` bits
        let lane_mask = !(u64::MAX >> lo);

        let lane_mask_v = b.ins().iconst(types::I64, lane_mask as i64);
        let mut out_v = if new_t.is_vector() {
            let zeroed = b.ins().iconst(types::I64, 0);
            Some(b.ins().splat(new_t, zeroed))
        } else {
            None
        };

        for lno in lane_lo..lane_hi {
            let lane_val = b.ins().extractlane(value, lno as u8);
            let lane_val = b.ins().rotr_imm_u(lane_val, lo as i64);
            let carry_bits = if lno < orig_t.lane_count() - 1 {
                let lane_tmp = b.ins().extractlane(value, (lno + 1) as u8);
                // let lane_v = b.ins().rotr_imm_u(lane_tmp, lo as i64);
                b.ins().band(lane_tmp, lane_mask_v)
            } else {
                b.ins().iconst(types::I64, 0)
            };
            // let lane_v = b.ins().extractlane(rot_l, lno as u8);
            let lane_lo = b.ins().band_not(lane_val, lane_mask_v);
            let with_carry = b.ins().bor(lane_lo, carry_bits);
            if let Some(ov) = out_v {
                out_v = Some(b.ins().insertlane(ov, with_carry, lno as u8));
            } else {
                // return the first thing
                if !new_t.eq(&types::I64) {
                    return b.ins().ireduce(new_t, with_carry);
                } else {
                    return with_carry;
                }
            }
        }
        return out_v.unwrap();

        // if new_t.is_vector() {
        //     // case: slice vec to vec
        //     // do the dumb thing, extract / insert lanes
        //     let zeroed = b.ins().iconst(types::I64, 0);
        //     let mut out_v = b.ins().splat(new_t, zeroed);

        //     for (olane, i) in ((lo / 64)..orig_t.lane_count()).enumerate() {
        //         let orig_lv = b.ins().extractlane(value, i as u8);
        //         out_v = b.ins().insertlane(out_v, orig_lv, olane as u8);
        //     }
        //     out_v
        // } else {
        //     // case: slice vec to int
        //     // extract lane, then reduce to correct type
        //     let extracted_ln = b.ins().extractlane(value, (lo / 64) as u8);
        //     let extracted_ln = b.ins().ushr_imm(extracted_ln, lo as i64);
        //     if !new_t.eq(&types::I64) {
        //         b.ins().ireduce(new_t, extracted_ln)
        //     } else {
        //         extracted_ln
        //     }
        // }
    } else {
        // case: slice int to int
        let tmp = mask(b, shifted, hi - lo + 1);
        if !orig_t.eq(&new_t) {
            b.ins().ireduce(new_t, tmp)
        } else {
            tmp // no need to reduce
        }
    }
}

// NOTE: the following are non-functional on wide bitvectors
// begin:
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
    extend_to_fit(b, arg, width - by, width)
}
pub fn sign_extend(b: &mut FunctionBuilder, arg: Value, by: WidthInt, width: WidthInt) -> Value {
    let mut ret = extend_to_fit(b, arg, width - by, width);
    let num_leading_zeros = select_container_primitive(width).bytes() * 8 - width;
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

pub fn implies(b: &mut FunctionBuilder, lhs: Value, rhs: Value, width: WidthInt) -> Value {
    let lhs = b.ins().bnot(lhs);
    let ret = b.ins().bor(lhs, rhs);
    mask(b, ret, width)
}

// end
