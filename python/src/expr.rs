use crate::ctx::{ContextGuardRead, ContextGuardWrite};
use ::patronus::expr::SerializableIrNode;
use baa::BitVecValue;
use num_bigint::BigInt;
use patronus::expr::{TypeCheck, WidthInt};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;

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
    fn __str__(&self) -> String {
        self.0.serialize_to_str(ContextGuardRead::default().deref())
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

    fn __eq__(&self, other: &Self) -> PyResult<Self> {
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

    fn __inv__(&self) -> PyResult<Self> {
        Ok(ExprRef(
            ContextGuardWrite::default().deref_mut().not(self.0),
        ))
    }

    fn __neg__(&self) -> PyResult<Self> {
        Ok(ExprRef(
            ContextGuardWrite::default().deref_mut().negate(self.0),
        ))
    }

    fn width(&self) -> Option<WidthInt> {
        let c = ContextGuardRead::default();
        c.deref()[self.0].get_bv_type(c.deref())
    }
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
