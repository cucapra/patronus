// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::Type;
use super::{Context, Expr, ExprRef};
use baa::BitVecOps;
use std::io::Write;

pub trait SerializableIrNode {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()>;
    fn serialize_to_str(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        self.serialize(ctx, &mut buf)
            .expect("Failed to write to string!");
        String::from_utf8(buf).expect("Failed to read string we wrote!")
    }
}

impl SerializableIrNode for Expr {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        serialize_expr(self, ctx, writer, &|_, _| Ok(true))
    }
}

/// Internal serialize function for expressions.
/// The `serialize_child` function determines whether the child expression is serialized
/// recursively or not. This can be used in order to limit the expression depth or the kinds
/// of expressions that should be serialized.
pub(crate) fn serialize_expr<F, W>(
    expr: &Expr,
    ctx: &Context,
    writer: &mut W,
    serialize_child: &F,
) -> std::io::Result<()>
where
    F: Fn(&ExprRef, &mut W) -> std::io::Result<bool>,
    W: Write,
{
    match expr {
        Expr::BVSymbol { name, .. } => write!(writer, "{}", ctx[*name]),
        Expr::BVLiteral(value) => {
            if value.width() <= 8 {
                write!(writer, "{}'b{}", value.width(), value.get(ctx).to_bit_str())
            } else {
                write!(writer, "{}'x{}", value.width(), value.get(ctx).to_hex_str())
            }
        }
        Expr::BVZeroExt { e, by, .. } => {
            write!(writer, "zext(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ", {by})")
        }
        Expr::BVSignExt { e, by, .. } => {
            write!(writer, "sext(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ", {by})")
        }
        Expr::BVSlice { e, hi, lo, .. } => {
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            if hi == lo {
                write!(writer, "[{hi}]")
            } else {
                write!(writer, "[{hi}:{lo}]")
            }
        }
        Expr::BVNot(e, _) => {
            write!(writer, "not(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVNegate(e, _) => {
            write!(writer, "neg(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVEqual(a, b) => {
            write!(writer, "eq(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVImplies(a, b) => {
            write!(writer, "implies(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreater(a, b) => {
            write!(writer, "ugt(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterSigned(a, b, _) => {
            write!(writer, "sgt(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterEqual(a, b) => {
            write!(writer, "ugte(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterEqualSigned(a, b, _) => {
            write!(writer, "sgte(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVConcat(a, b, _) => {
            write!(writer, "concat(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVAnd(a, b, _) => {
            write!(writer, "and(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVOr(a, b, _) => {
            write!(writer, "or(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVXor(a, b, _) => {
            write!(writer, "xor(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVShiftLeft(a, b, _) => {
            write!(writer, "shift_left(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVArithmeticShiftRight(a, b, _) => {
            write!(writer, "arithmetic_shift_right(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVShiftRight(a, b, _) => {
            write!(writer, "shift_right(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVAdd(a, b, _) => {
            write!(writer, "add(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVMul(a, b, _) => {
            write!(writer, "mul(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedDiv(a, b, _) => {
            write!(writer, "sdiv(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVUnsignedDiv(a, b, _) => {
            write!(writer, "udiv(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedMod(a, b, _) => {
            write!(writer, "smod(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedRem(a, b, _) => {
            write!(writer, "srem(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVUnsignedRem(a, b, _) => {
            write!(writer, "urem(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSub(a, b, _) => {
            write!(writer, "sub(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVArrayRead { array, index, .. } => {
            if (serialize_child)(array, writer)? {
                serialize_expr_ref(array, ctx, writer, serialize_child)?;
            }
            write!(writer, "[")?;
            if (serialize_child)(index, writer)? {
                serialize_expr_ref(index, ctx, writer, serialize_child)?;
            }
            write!(writer, "]")
        }
        Expr::BVIte {
            cond, tru, fals, ..
        } => {
            write!(writer, "ite(")?;
            if (serialize_child)(cond, writer)? {
                serialize_expr_ref(cond, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(tru, writer)? {
                serialize_expr_ref(tru, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(fals, writer)? {
                serialize_expr_ref(fals, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::ArraySymbol { name, .. } => write!(writer, "{}", ctx[*name]),
        Expr::ArrayConstant { e, index_width, .. } => {
            write!(writer, "([")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, "] x 2^{index_width})")
        }
        Expr::ArrayEqual(a, b) => {
            write!(writer, "eq(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::ArrayStore { array, index, data } => {
            if (serialize_child)(array, writer)? {
                serialize_expr_ref(array, ctx, writer, serialize_child)?;
            }
            write!(writer, "[")?;
            if (serialize_child)(index, writer)? {
                serialize_expr_ref(index, ctx, writer, serialize_child)?;
            }
            write!(writer, " := ")?;
            if (serialize_child)(data, writer)? {
                serialize_expr_ref(data, ctx, writer, serialize_child)?;
            }
            write!(writer, "]")
        }
        Expr::ArrayIte { cond, tru, fals } => {
            write!(writer, "ite(")?;
            if (serialize_child)(cond, writer)? {
                serialize_expr_ref(cond, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(tru, writer)? {
                serialize_expr_ref(tru, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(fals, writer)? {
                serialize_expr_ref(fals, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
    }
}

/// De-reference and serialize.
#[inline]
pub(crate) fn serialize_expr_ref<F, W>(
    expr: &ExprRef,
    ctx: &Context,
    writer: &mut W,
    serialize_child: &F,
) -> std::io::Result<()>
where
    F: Fn(&ExprRef, &mut W) -> std::io::Result<bool>,
    W: Write,
{
    serialize_expr(&ctx[*expr], ctx, writer, serialize_child)
}

impl SerializableIrNode for ExprRef {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        ctx[*self].serialize(ctx, writer)
    }
}

impl SerializableIrNode for Type {
    fn serialize<W: Write>(&self, _ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        write!(writer, "{}", self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_serialization() {
        let mut ctx = Context::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
