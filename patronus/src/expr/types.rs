// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

//! # Expression Types
//! Contains functions to check that an expression has consistent type information as
//! well as functions to access the type of correctly types expressions.

use super::{ArrayType, Context, Expr, ExprRef, Type};
use crate::expr::nodes::WidthInt;

#[derive(Debug, Clone)]
pub struct TypeCheckError {
    msg: String,
}

impl TypeCheckError {
    pub fn get_msg(&self) -> &str {
        &self.msg
    }
}

impl Type {
    fn expect_bv(&self, op: &str) -> Result<WidthInt, TypeCheckError> {
        match self {
            Type::BV(width) => Ok(*width),
            Type::Array(_) => Err(TypeCheckError {
                msg: format!("{op} only works on bit-vectors, not arrays."),
            }),
        }
    }
    fn expect_bv_of(&self, expected_width: WidthInt, op: &str) -> Result<Type, TypeCheckError> {
        match self {
            Type::BV(width) if *width == expected_width => Ok(*self),
            other => Err(TypeCheckError {
                msg: format!(
                    "{op} only works on bit-vectors of size {expected_width}, not {other:?}."
                ),
            }),
        }
    }
    fn expect_array(&self, op: &str) -> Result<ArrayType, TypeCheckError> {
        match self {
            Type::BV(w) => Err(TypeCheckError {
                msg: format!("{op} needs to be an array, not a bv<{w}>."),
            }),
            Type::Array(tpe) => Ok(*tpe),
        }
    }
}

fn expect_same_width_bvs(
    ctx: &Context,
    op: &str,
    a: ExprRef,
    b: ExprRef,
) -> Result<Type, TypeCheckError> {
    let a_width = a.get_type(ctx).expect_bv(op)?;
    let b_width = b.get_type(ctx).expect_bv(op)?;
    if a_width == b_width {
        Ok(Type::BV(a_width))
    } else {
        Err(TypeCheckError {
            msg: format!(
                "{op} requires two bit-vectors of the same width, not {a_width} and {b_width}"
            ),
        })
    }
}

fn expect_same_width_bvs_of(
    ctx: &Context,
    expected_width: WidthInt,
    op: &str,
    a: ExprRef,
    b: ExprRef,
) -> Result<Type, TypeCheckError> {
    expect_same_width_bvs(ctx, op, a, b)?.expect_bv_of(expected_width, op)
}

fn expect_same_size_arrays(
    ctx: &Context,
    op: &str,
    a: ExprRef,
    b: ExprRef,
) -> Result<Type, TypeCheckError> {
    let a_tpe = a.get_type(ctx).expect_array(op)?;
    let b_tpe = b.get_type(ctx).expect_array(op)?;
    if a_tpe == b_tpe {
        Ok(Type::Array(a_tpe))
    } else {
        Err(TypeCheckError {
            msg: format!("{op} requires two arrays of the same type, not {a_tpe:?} and {b_tpe:?}"),
        })
    }
}

impl Expr {
    #[inline]
    pub(crate) fn is_array_type(&self) -> bool {
        matches!(
            self,
            Expr::ArraySymbol { .. }
                | Expr::ArrayConstant { .. }
                | Expr::ArrayIte { .. }
                | Expr::ArrayStore { .. }
        )
    }

    #[inline]
    pub(crate) fn is_bv_type(&self) -> bool {
        !self.is_array_type()
    }
}

// TODO: get rid of this trait and let users just manually resolve ExprRef
pub trait TypeCheck {
    /// Type check expression node. Does not recurse to lower nodes.
    fn type_check(&self, ctx: &Context) -> Result<Type, TypeCheckError>;
    /// gets type as fast as possible without performing any checks
    fn get_type(&self, ctx: &Context) -> Type;
    fn get_bv_type(&self, ctx: &Context) -> Option<WidthInt> {
        if let Type::BV(width) = self.get_type(ctx) {
            Some(width)
        } else {
            None
        }
    }
    fn get_array_type(&self, ctx: &Context) -> Option<ArrayType> {
        if let Type::Array(tpe) = self.get_type(ctx) {
            Some(tpe)
        } else {
            None
        }
    }
    fn is_bool(&self, ctx: &Context) -> bool {
        self.get_bv_type(ctx) == Some(1)
    }
}

impl TypeCheck for Expr {
    fn type_check(&self, ctx: &Context) -> Result<Type, TypeCheckError> {
        match *self {
            Expr::BVSymbol { name: _, width } => Ok(Type::BV(width)),
            Expr::BVLiteral(value) => Ok(Type::BV(value.width())),
            Expr::BVZeroExt { e, by, width } => {
                e.get_type(ctx).expect_bv_of(width - by, "zero extend")?;
                Ok(Type::BV(width))
            }
            Expr::BVSignExt { e, by, width } => {
                e.get_type(ctx).expect_bv_of(width - by, "zero extend")?;
                Ok(Type::BV(width))
            }
            Expr::BVSlice { e, hi, lo } => {
                let e_width = e.get_type(ctx).expect_bv("slicing")?;
                if hi >= e_width {
                    Err(TypeCheckError {
                        msg: format!(
                            "Bit-slice upper index must be smaller than the width {e_width}. Not: {hi}"
                        ),
                    })
                } else if hi < lo {
                    Err(TypeCheckError {
                        msg: format!(
                            "Bit-slice upper index must be larger or the same as the lower index. But {hi} < {lo}"
                        ),
                    })
                } else {
                    Ok(Type::BV(hi - lo + 1))
                }
            }
            Expr::BVNot(e, width) => Ok(e.get_type(ctx).expect_bv_of(width, "not")?),
            Expr::BVNegate(e, width) => Ok(e.get_type(ctx).expect_bv_of(width, "not")?),
            Expr::BVEqual(a, b) => {
                expect_same_width_bvs(ctx, "bit-vector equality", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVImplies(a, b) => {
                a.get_type(ctx).expect_bv_of(1, "implies")?;
                b.get_type(ctx).expect_bv_of(1, "implies")?;
                Ok(Type::BV(1))
            }
            Expr::BVGreater(a, b) => {
                expect_same_width_bvs(ctx, "greater", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVGreaterSigned(a, b, _width) => {
                expect_same_width_bvs(ctx, "greater signed", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVGreaterEqual(a, b) => {
                expect_same_width_bvs(ctx, "greater or equals", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVGreaterEqualSigned(a, b, _width) => {
                expect_same_width_bvs(ctx, "greater or equals signed", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVConcat(a, b, width) => {
                let a_width = a.get_type(ctx).expect_bv("concat")?;
                let b_width = b.get_type(ctx).expect_bv("concat")?;
                let tpe = Type::BV(a_width + b_width);
                tpe.expect_bv_of(width, "concat")?;
                Ok(tpe)
            }
            Expr::BVAnd(a, b, width) => expect_same_width_bvs_of(ctx, width, "and", a, b),
            Expr::BVOr(a, b, width) => expect_same_width_bvs_of(ctx, width, "or", a, b),
            Expr::BVXor(a, b, width) => expect_same_width_bvs_of(ctx, width, "xor", a, b),
            Expr::BVShiftLeft(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "shift left", a, b)
            }
            Expr::BVArithmeticShiftRight(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "arithmetic shift right", a, b)
            }
            Expr::BVShiftRight(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "shift right", a, b)
            }
            Expr::BVAdd(a, b, width) => expect_same_width_bvs_of(ctx, width, "add", a, b),
            Expr::BVMul(a, b, width) => expect_same_width_bvs_of(ctx, width, "mul", a, b),
            Expr::BVSignedDiv(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "signed div", a, b)
            }
            Expr::BVUnsignedDiv(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "unsigned div", a, b)
            }
            Expr::BVSignedMod(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "signed mod", a, b)
            }
            Expr::BVSignedRem(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "signed rem", a, b)
            }
            Expr::BVUnsignedRem(a, b, width) => {
                expect_same_width_bvs_of(ctx, width, "unsigned rem", a, b)
            }
            Expr::BVSub(a, b, width) => expect_same_width_bvs_of(ctx, width, "subtraction", a, b),
            Expr::BVArrayRead {
                array,
                index,
                width,
            } => {
                let array_tpe = array
                    .get_type(ctx)
                    .expect_array("the first argument to the read operation")?;
                let index_width = index.get_type(ctx).expect_bv("array read index")?;
                if array_tpe.index_width != index_width {
                    Err(TypeCheckError {
                        msg: format!(
                            "Underlying array requires index width {index_width} not {0}",
                            array_tpe.index_width
                        ),
                    })
                } else if array_tpe.data_width != width {
                    Err(TypeCheckError {
                        msg: format!(
                            "Underlying array requires data width {width} not {0}",
                            array_tpe.index_width
                        ),
                    })
                } else {
                    Ok(Type::BV(array_tpe.data_width))
                }
            }
            Expr::BVIte { cond, tru, fals } => {
                cond.get_type(ctx).expect_bv_of(1, "ite condition")?;
                expect_same_width_bvs(ctx, "ite branches", tru, fals)
            }
            Expr::ArraySymbol {
                name: _,
                index_width,
                data_width,
            } => Ok(Type::Array(ArrayType {
                index_width,
                data_width,
            })),
            Expr::ArrayConstant {
                e,
                index_width,
                data_width,
            } => {
                e.get_type(ctx).expect_bv_of(data_width, "array constant")?;
                Ok(Type::Array(ArrayType {
                    index_width,
                    data_width,
                }))
            }
            Expr::ArrayEqual(a, b) => {
                expect_same_size_arrays(ctx, "the array equals operation", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::ArrayStore { array, index, data } => {
                let tpe = array
                    .get_type(ctx)
                    .expect_array("the first argument to the store operation")?;
                index
                    .get_type(ctx)
                    .expect_bv_of(tpe.index_width, "array store index")?;
                data.get_type(ctx)
                    .expect_bv_of(tpe.data_width, "array store data")?;
                Ok(Type::Array(tpe))
            }
            Expr::ArrayIte { cond, tru, fals } => {
                cond.get_type(ctx).expect_bv_of(1, "ite condition")?;
                expect_same_size_arrays(ctx, "both ite branches", tru, fals)
            }
        }
    }

    fn get_type(&self, ctx: &Context) -> Type {
        match *self {
            Expr::BVSymbol { name: _, width } => Type::BV(width),
            Expr::BVLiteral(value) => Type::BV(value.width()),
            Expr::BVZeroExt { e: _, by: _, width } => Type::BV(width),
            Expr::BVSignExt { e: _, by: _, width } => Type::BV(width),
            Expr::BVSlice { e: _, hi, lo } => Type::BV(hi - lo + 1),
            Expr::BVNot(_, width) => Type::BV(width),
            Expr::BVNegate(_, width) => Type::BV(width),
            Expr::BVEqual(_, _) => Type::BV(1),
            Expr::BVImplies(_, _) => Type::BV(1),
            Expr::BVGreater(_, _) => Type::BV(1),
            Expr::BVGreaterSigned(_, _, _) => Type::BV(1),
            Expr::BVGreaterEqual(_, _) => Type::BV(1),
            Expr::BVGreaterEqualSigned(_, _, _) => Type::BV(1),
            Expr::BVConcat(_, _, width) => Type::BV(width),
            Expr::BVAnd(_, _, width) => Type::BV(width),
            Expr::BVOr(_, _, width) => Type::BV(width),
            Expr::BVXor(_, _, width) => Type::BV(width),
            Expr::BVShiftLeft(_, _, width) => Type::BV(width),
            Expr::BVArithmeticShiftRight(_, _, width) => Type::BV(width),
            Expr::BVShiftRight(_, _, width) => Type::BV(width),
            Expr::BVAdd(_, _, width) => Type::BV(width),
            Expr::BVMul(_, _, width) => Type::BV(width),
            Expr::BVSignedDiv(_, _, width) => Type::BV(width),
            Expr::BVUnsignedDiv(_, _, width) => Type::BV(width),
            Expr::BVSignedMod(_, _, width) => Type::BV(width),
            Expr::BVSignedRem(_, _, width) => Type::BV(width),
            Expr::BVUnsignedRem(_, _, width) => Type::BV(width),
            Expr::BVSub(_, _, width) => Type::BV(width),
            Expr::BVArrayRead {
                array: _,
                index: _,
                width,
            } => Type::BV(width),
            Expr::BVIte {
                cond: _,
                tru: _,
                fals,
            } => {
                // Here we need to recourse because adding a `width` field to BVIte
                // would have blown up the size of `Expr`.
                // We assume that the `fals` branch is less likely to be a nested ITE.
                fals.get_type(ctx)
            }
            Expr::ArraySymbol {
                name: _,
                index_width,
                data_width,
            } => Type::Array(ArrayType {
                index_width,
                data_width,
            }),
            Expr::ArrayConstant {
                e: _,
                index_width,
                data_width,
            } => Type::Array(ArrayType {
                index_width,
                data_width,
            }),
            Expr::ArrayEqual(_, _) => Type::BV(1),
            Expr::ArrayStore { array, .. } => array.get_type(ctx),
            Expr::ArrayIte {
                cond: _,
                tru: _,
                fals,
            } => {
                // Here we need to recourse because adding a `width` field to BVIte
                // would have blown up the size of `Expr`.
                // We assume that the `fals` branch is less likely to be a nested ITE.
                fals.get_type(ctx)
            }
        }
    }
}
impl TypeCheck for ExprRef {
    fn type_check(&self, ctx: &Context) -> std::result::Result<Type, TypeCheckError> {
        ctx[*self].type_check(ctx)
    }

    fn get_type(&self, ctx: &Context) -> Type {
        ctx[*self].get_type(ctx)
    }
}
