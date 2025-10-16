use crate::ctx::{ContextGuardRead, ContextGuardWrite};
use ::patronus::expr::SerializableIrNode;
use patronus::expr::{TypeCheck, WidthInt};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;

#[pyclass]
#[derive(Clone)]
pub struct ExprRef(pub(crate) patronus::expr::ExprRef);

#[pymethods]
impl ExprRef {
    fn __str__(&self) -> String {
        self.0.serialize_to_str(ContextGuardRead::default().deref())
    }

    fn __lt__(&self, other: &Self) -> PyResult<Self> {
        match (self.width(), other.width()) {
            (Some(left), Some(right)) if left == right => {
                // we default to signed, just like z3
                // a < b <=> b > a
                Ok(ExprRef(
                    ContextGuardWrite::default()
                        .deref_mut()
                        .greater_signed(other.0, self.0),
                ))
            }
            _ => Err(PyTypeError::new_err(
                "Can only compare two bit vectors of the same width",
            )),
        }
    }

    fn __gt__(&self, other: &Self) -> PyResult<Self> {
        match (self.width(), other.width()) {
            (Some(left), Some(right)) if left == right => {
                // we default to signed, just like z3
                Ok(ExprRef(
                    ContextGuardWrite::default()
                        .deref_mut()
                        .greater_signed(self.0, other.0),
                ))
            }
            _ => Err(PyTypeError::new_err(
                "Can only compare two bit vectors of the same width",
            )),
        }
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
