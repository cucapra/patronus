// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ctx::{ContextGuardRead, ContextGuardWrite};
use ::patronus::expr::SerializableIrNode;
use baa::BitVecValue;
use num_bigint::BigInt;
use patronus::expr::{SparseExprMap, TypeCheck, WidthInt};
use pyo3::exceptions::{PyRuntimeError, PyTypeError};
use pyo3::prelude::*;
use pyo3::types::PySlice;
use std::ops::DerefMut;
use std::sync::{LazyLock, RwLock};

#[pyclass]
#[derive(Clone, Copy)]
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

    fn width(&self) -> Option<WidthInt> {
        let c = ContextGuardRead::default();
        c.deref()[self.0].get_bv_type(c.deref())
    }

    /// Compares reference equality.
    /// This is different from the Z3 API where `==` builds an SMT expressoion
    fn __eq__(&self, other: &Self) -> bool {
        self.0 == other.0
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
