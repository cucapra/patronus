// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::expr::Context;
use crate::expr::context::{ExprRef, StringRef};
use baa::{BitVecValueIndex, BitVecValueRef};
use std::fmt::Debug;

/// This type restricts the maximum width that a bit-vector type is allowed to have in our IR.
pub type WidthInt = baa::WidthInt;

/// Type wrapping an index to a bit vector value.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct BVLitValue(BitVecValueIndex);

impl BVLitValue {
    pub(crate) fn new(index: BitVecValueIndex) -> Self {
        Self(index)
    }

    pub fn get<'c>(&self, ctx: &'c Context) -> BitVecValueRef<'c> {
        ctx.get_bv_value(self.0)
    }
    pub fn width(&self) -> WidthInt {
        self.0.width()
    }
    pub fn is_true(&self) -> bool {
        // this relies on the value interner always assigning index 1 to the number 1
        self.width() == 1 && self.0.is_one()
    }
    pub fn is_false(&self) -> bool {
        // this relies on the value interner always assigning index 0 to the number 0
        self.width() == 1 && self.0.is_zero()
    }
}

/// Represents a SMT bit-vector or array expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Expr {
    // Bit-Vector Expressions
    // nullary
    BVSymbol {
        name: StringRef,
        width: WidthInt,
    },
    BVLiteral(BVLitValue),
    // unary operations
    BVZeroExt {
        e: ExprRef,
        by: WidthInt,
        width: WidthInt,
    },
    BVSignExt {
        e: ExprRef,
        by: WidthInt,
        width: WidthInt,
    },
    BVSlice {
        e: ExprRef,
        hi: WidthInt,
        lo: WidthInt,
        // no `width` since it is easy to calculate from `hi` and `lo` without looking at `e`
    },
    BVNot(ExprRef, WidthInt),
    BVNegate(ExprRef, WidthInt),
    // binary operations
    BVEqual(ExprRef, ExprRef),
    BVImplies(ExprRef, ExprRef),
    BVGreater(ExprRef, ExprRef),
    BVGreaterSigned(ExprRef, ExprRef, WidthInt), // width for easier implementation in the simulator
    BVGreaterEqual(ExprRef, ExprRef),
    BVGreaterEqualSigned(ExprRef, ExprRef, WidthInt), // width for easier implementation in the simulator
    BVConcat(ExprRef, ExprRef, WidthInt),
    // binary arithmetic
    BVAnd(ExprRef, ExprRef, WidthInt),
    BVOr(ExprRef, ExprRef, WidthInt),
    BVXor(ExprRef, ExprRef, WidthInt),
    BVShiftLeft(ExprRef, ExprRef, WidthInt),
    BVArithmeticShiftRight(ExprRef, ExprRef, WidthInt),
    BVShiftRight(ExprRef, ExprRef, WidthInt),
    BVAdd(ExprRef, ExprRef, WidthInt),
    BVMul(ExprRef, ExprRef, WidthInt),
    BVSignedDiv(ExprRef, ExprRef, WidthInt),
    BVUnsignedDiv(ExprRef, ExprRef, WidthInt),
    BVSignedMod(ExprRef, ExprRef, WidthInt),
    BVSignedRem(ExprRef, ExprRef, WidthInt),
    BVUnsignedRem(ExprRef, ExprRef, WidthInt),
    BVSub(ExprRef, ExprRef, WidthInt),
    //
    BVArrayRead {
        array: ExprRef,
        index: ExprRef,
        width: WidthInt,
    },
    // ternary op
    BVIte {
        cond: ExprRef,
        tru: ExprRef,
        fals: ExprRef,
        // no width since that would increase the Expr size by 8 bytes (b/c of alignment)
        // width: WidthInt
    },
    // Array Expressions
    // nullary
    ArraySymbol {
        name: StringRef,
        index_width: WidthInt,
        data_width: WidthInt,
    },
    // unary
    ArrayConstant {
        e: ExprRef,
        index_width: WidthInt,
        data_width: WidthInt, // extra info since we have space
    },
    // binary
    ArrayEqual(ExprRef, ExprRef),
    // ternary
    ArrayStore {
        array: ExprRef,
        index: ExprRef,
        data: ExprRef,
    },
    ArrayIte {
        cond: ExprRef,
        tru: ExprRef,
        fals: ExprRef,
    },
}

impl Expr {
    /// Creates a symbol that matches the given `Type`.
    pub fn symbol(name: StringRef, tpe: Type) -> Expr {
        match tpe {
            Type::BV(width) => Expr::BVSymbol { name, width },
            Type::Array(ArrayType {
                data_width,
                index_width,
            }) => Expr::ArraySymbol {
                name,
                data_width,
                index_width,
            },
        }
    }

    pub fn is_symbol(&self) -> bool {
        matches!(self, Expr::BVSymbol { .. } | Expr::ArraySymbol { .. })
    }

    pub fn is_bv_lit(&self) -> bool {
        matches!(self, Expr::BVLiteral { .. })
    }

    /// Returns the reference to the symbol name. Returns `None` if the expression is not a symbol.
    pub fn get_symbol_name_ref(&self) -> Option<StringRef> {
        match self {
            Expr::BVSymbol { name, .. } => Some(*name),
            Expr::ArraySymbol { name, .. } => Some(*name),
            _ => None,
        }
    }

    pub fn get_symbol_name<'a>(&self, ctx: &'a Context) -> Option<&'a str> {
        self.get_symbol_name_ref().map(|r| ctx[r].as_str())
    }

    pub fn is_true(&self) -> bool {
        match self {
            Expr::BVLiteral(v) => v.is_true(),
            _ => false,
        }
    }

    pub fn is_false(&self) -> bool {
        match self {
            Expr::BVLiteral(v) => v.is_false(),
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct BVType(WidthInt);
#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct ArrayType {
    pub index_width: WidthInt,
    pub data_width: WidthInt,
}

impl ArrayType {
    pub fn data_type(&self) -> Type {
        Type::BV(self.data_width)
    }
    pub fn index_type(&self) -> Type {
        Type::BV(self.index_width)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Type {
    BV(WidthInt),
    Array(ArrayType),
}

impl Type {
    pub const BOOL: Type = Type::BV(1);
    pub fn is_bit_vector(&self) -> bool {
        match &self {
            Type::BV(_) => true,
            Type::Array(_) => false,
        }
    }

    pub fn is_array(&self) -> bool {
        match &self {
            Type::BV(_) => false,
            Type::Array(_) => true,
        }
    }

    pub fn is_bool(&self) -> bool {
        match &self {
            Type::BV(width) => *width == 1,
            Type::Array(_) => false,
        }
    }

    pub fn get_bit_vector_width(&self) -> Option<WidthInt> {
        match &self {
            Type::BV(width) => Some(*width),
            Type::Array(_) => None,
        }
    }

    pub fn get_array_data_width(&self) -> Option<WidthInt> {
        match &self {
            Type::BV(_) => None,
            Type::Array(a) => Some(a.data_width),
        }
    }

    pub fn get_array_index_width(&self) -> Option<WidthInt> {
        match &self {
            Type::BV(_) => None,
            Type::Array(a) => Some(a.index_width),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Type::BV(width) => write!(f, "bv<{width}>"),
            Type::Array(ArrayType {
                index_width,
                data_width,
            }) => write!(f, "bv<{index_width}> -> bv<{data_width}>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        // 4 bytes for the tag, 3  * 4 bytes for the largest field
        assert_eq!(std::mem::size_of::<Expr>(), 16);
        // we only represents widths up to (2^32 - 1)
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // an array has a index and a data width
        assert_eq!(std::mem::size_of::<ArrayType>(), 2 * 4);
        // Type could be a bit-vector or an array type (4 bytes for the tag!)
        assert_eq!(std::mem::size_of::<Type>(), 2 * 4 + 4);
    }
}
