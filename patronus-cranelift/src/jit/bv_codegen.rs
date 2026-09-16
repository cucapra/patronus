// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>

use baa::{BitVecOps, BitVecValueRef};
use cranelift::prelude::*;
use patronus::expr::*;

use super::compiler::{CodeGenContext, TaggedValue};

/// Contains width of result bit vector type.
pub(super) struct BVWord(pub(super) WidthInt);

macro_rules! iconst {
    ($ctx: expr, $value: expr) => {
        $ctx.fn_builder.ins().iconst($ctx.int, ($value) as i64)
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

impl BVWord {
    pub(super) fn new(width: WidthInt) -> Self {
        Self(width)
    }

    /// Unsigned extend input `value` to fit target width.
    pub(super) fn extend_to_fit(&self, value: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        debug_assert!(self.0 >= value.expect_bv_type());
        let prev_type = select_container_primitive(value.expect_bv_type());
        let target_type = select_container_primitive(self.0);
        if !prev_type.eq(&target_type) {
            ctx.fn_builder.ins().uextend(target_type, *value)
        } else {
            *value
        }
    }

    pub(super) fn truncate_to_fit(&self, value: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        debug_assert!(self.0 <= value.expect_bv_type());
        let prev_type = select_container_primitive(value.expect_bv_type());
        let target_type = select_container_primitive(self.0);
        if !prev_type.eq(&target_type) {
            ctx.fn_builder.ins().ireduce(target_type, *value)
        } else {
            *value
        }
    }

    fn overflow_guard(&self, value: Value, ctx: &mut CodeGenContext) -> Value {
        self.mask(value, self.0, ctx)
    }

    fn mask(&self, value: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width < 64 {
            ctx.fn_builder
                .ins()
                .band_imm(value, ((u64::MAX) >> (64 - width)) as i64)
        } else {
            value
        }
    }

    fn cmp(&self, lhs: Value, rhs: Value, condcode: IntCC, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().icmp(condcode, lhs, rhs)
    }

    pub fn symbol(&self, arg: ExprRef, ctx: &mut CodeGenContext) -> Value {
        let value = ctx.load_input_state(arg);
        // TODO: currently bv symbol is always stored as `i64`
        self.truncate_to_fit(TaggedValue::tag_bv(*value, 64), ctx)
    }

    pub fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().iconst(
            select_container_primitive(self.0),
            value.to_u64().unwrap() as i64,
        )
    }

    pub fn add(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().iadd(*lhs, *rhs), ctx)
    }
    pub fn sub(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().isub(*lhs, *rhs), ctx)
    }
    pub fn mul(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().imul(*lhs, *rhs), ctx)
    }

    pub fn and(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().band(*lhs, *rhs)
    }
    pub fn or(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bor(*lhs, *rhs)
    }
    pub fn xor(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bxor(*lhs, *rhs)
    }

    pub fn not(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().bnot(*arg), ctx)
    }
    pub fn negate(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        let flipped = ctx.fn_builder.ins().bnot(*arg);
        self.overflow_guard(ctx.fn_builder.ins().iadd_imm(flipped, 1), ctx)
    }

    pub fn zero_extend(&self, arg: TaggedValue, _by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        self.extend_to_fit(arg, ctx)
    }
    pub fn sign_extend(&self, arg: TaggedValue, _by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        let mut ret = self.extend_to_fit(arg, ctx);
        let num_leading_zeros =
            select_container_primitive(self.0).bytes() * 8 - arg.expect_bv_type();
        if num_leading_zeros != 0 {
            let shifted = ctx.fn_builder.ins().ishl_imm(ret, num_leading_zeros as i64);
            ret = ctx
                .fn_builder
                .ins()
                .sshr_imm(shifted, num_leading_zeros as i64);
        }
        self.overflow_guard(ret, ctx)
    }

    pub fn shift_right(
        &self,
        arg0: TaggedValue,
        arg1: TaggedValue,
        ctx: &mut CodeGenContext,
    ) -> Value {
        assert!(!arg1.requires_bv_delegation());
        self.truncate_to_fit(
            TaggedValue::tag_bv(
                ctx.fn_builder.ins().ushr(*arg0, *arg1),
                arg0.expect_bv_type(),
            ),
            ctx,
        )
    }
    pub fn arithmetic_shift_right(
        &self,
        arg0: TaggedValue,
        arg1: TaggedValue,
        ctx: &mut CodeGenContext,
    ) -> Value {
        assert!(!arg1.requires_bv_delegation());
        self.truncate_to_fit(
            TaggedValue::tag_bv(
                ctx.fn_builder.ins().sshr(*arg0, *arg1),
                arg0.expect_bv_type(),
            ),
            ctx,
        )
    }
    pub fn shift_left(
        &self,
        arg0: TaggedValue,
        arg1: TaggedValue,
        ctx: &mut CodeGenContext,
    ) -> Value {
        assert!(!arg1.requires_bv_delegation());
        let arg0 = self.extend_to_fit(arg0, ctx);
        self.overflow_guard(ctx.fn_builder.ins().ishl(arg0, *arg1), ctx)
    }

    pub fn equal(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!lhs.requires_bv_delegation());

        self.cmp(*lhs, *rhs, IntCC::Equal, ctx)
    }
    pub fn gt(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!lhs.requires_bv_delegation());

        self.cmp(*lhs, *rhs, IntCC::UnsignedGreaterThan, ctx)
    }
    pub fn ge(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!lhs.requires_bv_delegation());
        self.cmp(*lhs, *rhs, IntCC::UnsignedGreaterThanOrEqual, ctx)
    }
    pub fn gt_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!lhs.requires_bv_delegation());
        self.cmp(*lhs, *rhs, IntCC::SignedGreaterThan, ctx)
    }

    pub fn ge_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!lhs.requires_bv_delegation());
        self.cmp(*lhs, *rhs, IntCC::SignedGreaterThanOrEqual, ctx)
    }

    pub fn concat(&self, hi: TaggedValue, lo: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        let lo_width = lo.expect_bv_type();
        let (hi, lo) = (self.extend_to_fit(hi, ctx), self.extend_to_fit(lo, ctx));
        let hi = ctx.fn_builder.ins().ishl_imm(hi, lo_width as i64);
        ctx.fn_builder.ins().bor(hi, lo)
    }

    pub fn slice(
        &self,
        value: TaggedValue,
        hi: WidthInt,
        lo: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        assert!(!value.requires_bv_delegation());

        let shifted = self.truncate_to_fit(
            TaggedValue::tag_bv(
                ctx.fn_builder.ins().ushr_imm(*value, lo as i64),
                value.expect_bv_type(),
            ),
            ctx,
        );
        self.mask(shifted, hi - lo + 1, ctx)
    }
    pub fn implies(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        let lhs = ctx.fn_builder.ins().bnot(*lhs);
        let ret = ctx.fn_builder.ins().bor(lhs, *rhs);
        self.overflow_guard(ret, ctx)
    }
}
