// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::TransitionSystem;
use crate::ctx::{ContextGuardRead, ContextGuardWrite};
use ::patronus::expr::SerializableIrNode;
use baa::BitVecValue;
use either::Either;
use num_bigint::BigInt;
use patronus::expr::{
    ArrayType, Expr, ForEachChild, SparseExprMap, StringRef, Type, TypeCheck, WidthInt,
    find_symbols,
};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::DerefMut;
use std::sync::{LazyLock, RwLock};

#[pyclass(from_py_object)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprRef(pub(crate) patronus::expr::ExprRef);

/// Helper for binary ops that require a and b to be bitvectors of the same width
fn bv_bin_op(
    a: &ExprRef,
    b: &ExprRef,
    op_str: &str,
    op: fn(
        &mut patronus::expr::Context,
        patronus::expr::ExprRef,
        patronus::expr::ExprRef,
    ) -> patronus::expr::ExprRef,
) -> PyResult<ExprRef> {
    match (a.width(), b.width()) {
        (Some(left), Some(right)) if left == right => {
            let mut guard = ContextGuardWrite::default();
            let res = op(guard.deref_mut(), a.0, b.0);
            Ok(ExprRef(res))
        }
        _ => Err(PyTypeError::new_err(format!(
            "Can only apply {op_str} two bit vectors of the same width"
        ))),
    }
}

#[pymethods]
impl ExprRef {
    pub(crate) fn __str__(&self) -> String {
        self.0.serialize_to_str(ContextGuardRead::default().deref())
    }

    fn __repr__(&self) -> String {
        self.__str__()
    }

    fn __lt__(&self, other: &Self) -> PyResult<Self> {
        // we default to signed, just like z3
        // a < b <=> b > a
        bv_bin_op(self, other, "less than", |ctx, a, b| {
            ctx.greater_signed(b, a)
        })
    }

    fn __gt__(&self, other: &Self) -> PyResult<Self> {
        // we default to signed, just like z3
        bv_bin_op(self, other, "greater than", |ctx, a, b| {
            ctx.greater_signed(a, b)
        })
    }

    fn equals(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "equal", |ctx, a, b| ctx.equal(a, b))
    }

    fn __add__(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "add", |ctx, a, b| ctx.add(a, b))
    }

    fn __sub__(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "sub", |ctx, a, b| ctx.sub(a, b))
    }

    fn __mul__(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "mul", |ctx, a, b| ctx.mul(a, b))
    }

    fn __or__(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "or", |ctx, a, b| ctx.or(a, b))
    }

    fn __and__(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "and", |ctx, a, b| ctx.and(a, b))
    }

    fn __xor__(&self, other: &Self) -> PyResult<Self> {
        bv_bin_op(self, other, "xor", |ctx, a, b| ctx.xor(a, b))
    }

    fn __invert__(&self) -> PyResult<Self> {
        Ok(ExprRef(
            ContextGuardWrite::default().deref_mut().not(self.0),
        ))
    }

    fn __neg__(&self) -> PyResult<Self> {
        Ok(ExprRef(
            ContextGuardWrite::default().deref_mut().negate(self.0),
        ))
    }

    // TODO: find a way to accept "invalid" slices
    // fn __getitem__<'py>(&self, index: Bound<'py, PySlice>)-> PyResult<Self> {
    //     let mut guard = ContextGuardWrite::default();
    //     let ctx = guard.deref_mut();
    //     if let Some(width) = ctx[self.0].get_bv_type(ctx) {
    //         let indices = index.as_borrowed().indices(width as isize)?;
    //         Ok(ExprRef(ctx.slice(self.0, indices.stop as WidthInt, indices.start as WidthInt)))
    //     } else {
    //         Err(PyRuntimeError::new_err("Can only slice bit vectors!"))
    //     }
    //
    // }

    fn __getitem__<'py>(&self, index: ExprRef) -> PyResult<Self> {
        let mut guard = ContextGuardWrite::default();
        let ctx = guard.deref_mut();
        match self.0.get_type(ctx) {
            Type::BV(_) => {
                todo!("add support for bit vector slices")
            }
            Type::Array(_) => Ok(Self(ctx.array_read(self.0, index.0))),
        }
    }

    fn width(&self) -> Option<WidthInt> {
        let c = ContextGuardRead::default();
        c.deref()[self.0].get_bv_type(c.deref())
    }

    /// Compares reference equality.
    /// This is different from the Z3 API where `==` builds an SMT expressoion
    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn __hash__(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.0.hash(&mut hasher);
        hasher.finish()
    }

    fn op(&self) -> Op {
        (&ContextGuardRead::default().deref()[self.0]).into()
    }

    fn args(&self) -> Vec<Self> {
        let mut children = vec![];
        ContextGuardRead::default().deref()[self.0].collect_children(&mut children);
        children.into_iter().map(ExprRef).collect()
    }

    fn children(&self) -> Vec<Self> {
        self.args()
    }

    fn name(&self) -> Option<String> {
        ContextGuardRead::default()
            .deref()
            .get_symbol_name(self.0)
            .map(|s| s.to_string())
    }

    fn symbols(&self) -> FxHashSet<Self> {
        find_symbols(ContextGuardRead::default().deref(), self.0)
            .into_iter()
            .map(Self)
            .collect()
    }

    fn replace(&self, map: FxHashMap<Self, Self>) -> Self {
        let map: FxHashMap<_, _> = map.into_iter().map(|(k, v)| (k.0, v.0)).collect();
        let e = patronus::expr::simple_transform_expr(
            ContextGuardWrite::default().deref_mut(),
            self.0,
            |_, e, _| map.get(&e).cloned(),
        );
        Self(e)
    }

    fn sort(&self) -> Either<BitVecSort, ArraySort> {
        match self.0.get_type(ContextGuardRead::default().deref()) {
            Type::BV(width) => Either::Left(BitVecSort(width)),
            Type::Array(a) => Either::Right(a.into()),
        }
    }
}

#[pyclass(eq, eq_int)]
#[derive(PartialEq)]
pub enum Op {
    BVSymbol,
    BVLiteral,
    BVZeroExt,
    BVSignExt,
    BVSlice,
    BVNot,
    BVNegate,
    BVEqual,
    BVImplies,
    BVGreater,
    BVGreaterSigned,
    BVGreaterEqual,
    BVGreaterEqualSigned,
    BVConcat,
    BVAnd,
    BVOr,
    BVXor,
    BVShiftLeft,
    BVArithmeticShiftRight,
    BVShiftRight,
    BVAdd,
    BVMul,
    BVSignedDiv,
    BVUnsignedDiv,
    BVSignedMod,
    BVSignedRem,
    BVUnsignedRem,
    BVSub,
    BVArrayRead,
    BVIte,
    ArraySymbol,
    ArrayConstant,
    ArrayEqual,
    ArrayStore,
    ArrayIte,
}

impl From<&patronus::expr::Expr> for Op {
    fn from(value: &Expr) -> Self {
        match value {
            Expr::BVSymbol { .. } => Op::BVSymbol,
            Expr::BVLiteral(_) => Op::BVLiteral,
            Expr::BVZeroExt { .. } => Op::BVZeroExt,
            Expr::BVSignExt { .. } => Op::BVSignExt,
            Expr::BVSlice { .. } => Op::BVSlice,
            Expr::BVNot(_, _) => Op::BVNot,
            Expr::BVNegate(_, _) => Op::BVNegate,
            Expr::BVEqual(_, _) => Op::BVEqual,
            Expr::BVImplies(_, _) => Op::BVImplies,
            Expr::BVGreater(_, _) => Op::BVGreater,
            Expr::BVGreaterSigned(_, _, _) => Op::BVGreaterSigned,
            Expr::BVGreaterEqual(_, _) => Op::BVGreaterEqual,
            Expr::BVGreaterEqualSigned(_, _, _) => Op::BVGreaterEqualSigned,
            Expr::BVConcat(_, _, _) => Op::BVConcat,
            Expr::BVAnd(_, _, _) => Op::BVAnd,
            Expr::BVOr(_, _, _) => Op::BVOr,
            Expr::BVXor(_, _, _) => Op::BVXor,
            Expr::BVShiftLeft(_, _, _) => Op::BVShiftLeft,
            Expr::BVArithmeticShiftRight(_, _, _) => Op::BVArithmeticShiftRight,
            Expr::BVShiftRight(_, _, _) => Op::BVShiftRight,
            Expr::BVAdd(_, _, _) => Op::BVAdd,
            Expr::BVMul(_, _, _) => Op::BVMul,
            Expr::BVSignedDiv(_, _, _) => Op::BVSignedDiv,
            Expr::BVUnsignedDiv(_, _, _) => Op::BVUnsignedDiv,
            Expr::BVSignedMod(_, _, _) => Op::BVSignedMod,
            Expr::BVSignedRem(_, _, _) => Op::BVSignedRem,
            Expr::BVUnsignedRem(_, _, _) => Op::BVUnsignedRem,
            Expr::BVSub(_, _, _) => Op::BVSub,
            Expr::BVArrayRead { .. } => Op::BVArrayRead,
            Expr::BVIte { .. } => Op::BVIte,
            Expr::ArraySymbol { .. } => Op::ArraySymbol,
            Expr::ArrayConstant { .. } => Op::ArrayConstant,
            Expr::ArrayEqual(_, _) => Op::ArrayEqual,
            Expr::ArrayStore { .. } => Op::ArrayStore,
            Expr::ArrayIte { .. } => Op::ArrayIte,
        }
    }
}

#[pymethods]
impl Op {
    fn snake_case(&self) -> String {
        let cc = match self {
            Op::BVSymbol => "bv_symbol",
            Op::BVLiteral => "bv_literal",
            Op::BVZeroExt => "bv_zero_ext",
            Op::BVSignExt => "bv_sign_ext",
            Op::BVSlice => "bv_slice",
            Op::BVNot => "bv_not",
            Op::BVNegate => "bv_negate",
            Op::BVEqual => "bv_equal",
            Op::BVImplies => "bv_implies",
            Op::BVGreater => "bv_greater",
            Op::BVGreaterSigned => "bv_greater_signed",
            Op::BVGreaterEqual => "bv_greater_equal",
            Op::BVGreaterEqualSigned => "bv_greater_equal_signed",
            Op::BVConcat => "bv_concat",
            Op::BVAnd => "bv_and",
            Op::BVOr => "bv_or",
            Op::BVXor => "bv_xor",
            Op::BVShiftLeft => "bv_shift_left",
            Op::BVArithmeticShiftRight => "bv_arithmetic_shift_right",
            Op::BVShiftRight => "bv_shift_right",
            Op::BVAdd => "bv_add",
            Op::BVMul => "bv_mul",
            Op::BVSignedDiv => "bv_signed_div",
            Op::BVUnsignedDiv => "bv_unsigned_div",
            Op::BVSignedMod => "bv_signed_mod",
            Op::BVSignedRem => "bv_signed_rem",
            Op::BVUnsignedRem => "bv_unsigned_rem",
            Op::BVSub => "bv_sub",
            Op::BVArrayRead => "bv_array_read",
            Op::BVIte => "bv_ite",
            Op::ArraySymbol => "array_symbol",
            Op::ArrayConstant => "array_constant",
            Op::ArrayEqual => "array_equal",
            Op::ArrayStore => "array_store",
            Op::ArrayIte => "array_ite",
        };
        cc.into()
    }
}

/// Simplifier that is used by default for all operations.
/// Python usage is expected to be less performance critical, so using a single global
/// simplifier seems acceptable and will simplify use.
static DEFAULT_SIMPLIFIER: LazyLock<
    RwLock<::patronus::expr::Simplifier<SparseExprMap<Option<::patronus::expr::ExprRef>>>>,
> = LazyLock::new(|| RwLock::new(::patronus::expr::Simplifier::new(SparseExprMap::default())));

#[pyfunction]
pub fn simplify(e: ExprRef) -> ExprRef {
    let mut guard = DEFAULT_SIMPLIFIER.write().unwrap();
    let r = guard
        .deref_mut()
        .simplify(ContextGuardWrite::default().deref_mut(), e.0);
    ExprRef(r)
}

#[pyfunction]
#[pyo3(name = "BitVec")]
pub fn bit_vec(name: &str, width: WidthInt) -> ExprRef {
    ExprRef(
        ContextGuardWrite::default()
            .deref_mut()
            .bv_symbol(name, width),
    )
}

#[pyfunction]
#[pyo3(name = "BitVecVal")]
pub fn bit_vec_val(value: BigInt, width: WidthInt) -> ExprRef {
    let value = BitVecValue::from_big_int(&value, width);
    ExprRef(ContextGuardWrite::default().deref_mut().bv_lit(&value))
}

#[pyclass(from_py_object, eq)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitVecSort(WidthInt);

#[pymethods]
impl BitVecSort {
    #[new]
    fn create(width: WidthInt) -> Self {
        Self(width)
    }

    fn __str__(&self) -> String {
        format!("BitVec({})", self.0)
    }
}

#[pyclass(from_py_object, eq)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArraySort(BitVecSort, BitVecSort);

impl From<ArrayType> for ArraySort {
    fn from(value: ArrayType) -> Self {
        Self(BitVecSort(value.index_width), BitVecSort(value.data_width))
    }
}

#[pymethods]
impl ArraySort {
    #[new]
    fn create(index: Either<WidthInt, BitVecSort>, data: Either<WidthInt, BitVecSort>) -> Self {
        let index_width: WidthInt = index.map_right(|s| s.0).either_into();
        let data_width: WidthInt = data.map_right(|s| s.0).either_into();
        Self(BitVecSort(index_width), BitVecSort(data_width))
    }

    fn __str__(&self) -> String {
        format!("Array({}, {})", self.0.__str__(), self.1.__str__())
    }

    fn index_width(&self) -> WidthInt {
        self.0.0
    }

    fn data_width(&self) -> WidthInt {
        self.1.0
    }
}

#[pyfunction]
#[pyo3(name = "BoolSort")]
pub fn bool_sort() -> BitVecSort {
    BitVecSort(1)
}

#[pyfunction]
#[pyo3(name = "Array")]
pub fn array(
    name: &str,
    index: Either<WidthInt, BitVecSort>,
    data: Either<WidthInt, BitVecSort>,
) -> ExprRef {
    let tpe = ArraySort::create(index, data);
    ExprRef(ContextGuardWrite::default().deref_mut().array_symbol(
        name,
        tpe.index_width(),
        tpe.data_width(),
    ))
}

#[pyfunction]
#[pyo3(name = "ConstArray")]
pub fn const_array(index: Either<WidthInt, BitVecSort>, data: ExprRef) -> ExprRef {
    let index_width = index.map_right(|s| s.0).either_into();
    ExprRef(
        ContextGuardWrite::default()
            .deref_mut()
            .array_const(data.0, index_width),
    )
}

#[pyfunction]
#[pyo3(name = "K")]
pub fn const_array_z3_alias(index: Either<WidthInt, BitVecSort>, data: ExprRef) -> ExprRef {
    const_array(index, data)
}

#[pyfunction]
#[pyo3(name = "If")]
pub fn if_expr(cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
    ExprRef(
        ContextGuardWrite::default()
            .deref_mut()
            .ite(cond.0, tru.0, fals.0),
    )
}

#[pyfunction]
#[pyo3(name = "Store")]
pub fn array_store(array: ExprRef, index: ExprRef, data: ExprRef) -> ExprRef {
    ExprRef(
        ContextGuardWrite::default()
            .deref_mut()
            .array_store(array.0, index.0, data.0),
    )
}

#[pyfunction]
#[pyo3(name = "Update")]
pub fn array_store_alias(array: ExprRef, index: ExprRef, data: ExprRef) -> ExprRef {
    array_store(array, index, data)
}

#[pyfunction]
#[pyo3(name = "Select")]
pub fn array_select(array: ExprRef, index: ExprRef) -> ExprRef {
    array.__getitem__(index).unwrap()
}

#[pyfunction]
#[pyo3(name = "SignExt")]
pub fn sext(n: WidthInt, a: ExprRef) -> ExprRef {
    ExprRef(ContextGuardWrite::default().deref_mut().sign_extend(a.0, n))
}

#[pyfunction]
#[pyo3(name = "ZeroExt")]
pub fn zext(n: WidthInt, a: ExprRef) -> ExprRef {
    ExprRef(ContextGuardWrite::default().deref_mut().zero_extend(a.0, n))
}

#[pyfunction]
#[pyo3(name = "Extract")]
pub fn extract(high: WidthInt, low: WidthInt, a: ExprRef) -> ExprRef {
    slice(high, low, a)
}

#[pyfunction]
#[pyo3(name = "Slice")]
pub fn slice(high: WidthInt, low: WidthInt, a: ExprRef) -> ExprRef {
    ExprRef(
        ContextGuardWrite::default()
            .deref_mut()
            .slice(a.0, high, low),
    )
}
