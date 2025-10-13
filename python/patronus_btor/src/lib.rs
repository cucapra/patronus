use pyo3::exceptions::{PyIOError, PyIndexError, PyValueError};
use pyo3::prelude::*;
use baa::BitVecOps;
use patronus::btor2;
use patronus::expr::{Context, Expr, ExprRef};
use patronus::system::TransitionSystem;

#[pyclass]
pub struct Design {
    ctx: Context,
    sys: TransitionSystem,
}

#[pymethods]
impl Design {
    fn __len__(&self) -> usize {
        self.ctx.num_exprs()
    }

    fn __getitem__(&self, idx: isize, py: Python<'_>) -> PyResult<PyObject> {
        let n = self.ctx.num_exprs() as isize;
        let mut i = idx;
        if i < 0 {
            i += n;
        }
        if i < 0 || i >= n {
            return Err(PyIndexError::new_err(format!(
                "index {idx} out of range for length {n}"
            )));
        }
        let idx_u = i as usize;
        let r = ExprRef::from_index(idx_u);
        let e = self.ctx.get_expr(r);
        let d = expr_to_dict(py, e, &self.ctx)?;
        Ok(d)
    }

    // Optional convenience: number of roots of various categories
    #[pyo3(name = "num_states")]
    fn num_states_py(&self) -> usize {
        self.sys.states.len()
    }

    #[pyo3(name = "num_inputs")]
    fn num_inputs_py(&self) -> usize {
        self.sys.inputs.len()
    }

    #[pyo3(name = "num_outputs")]
    fn num_outputs_py(&self) -> usize {
        self.sys.outputs.len()
    }

    // Optional: names available at the system level
    #[pyo3(name = "name")]
    fn name_py(&self) -> String {
        self.sys.name.clone()
    }

    // Convenience lists for Python traversal
    #[pyo3(name = "inputs")]
    fn inputs_py(&self) -> Vec<usize> {
        self.sys
            .inputs
            .iter()
            .map(|&e| self.ctx.expr_index(e))
            .collect()
    }

    #[pyo3(name = "states")]
    fn states_py(&self) -> Vec<usize> {
        self.sys
            .states
            .iter()
            .map(|s| self.ctx.expr_index(s.symbol))
            .collect()
    }

    #[pyo3(name = "outputs")]
    fn outputs_py(&self) -> Vec<usize> {
        self.sys
            .outputs
            .iter()
            .map(|o| self.ctx.expr_index(o.expr))
            .collect()
    }

    #[pyo3(name = "find_symbol")]
    fn find_symbol_py(&self, name: &str) -> Option<usize> {
        let map = self.sys.get_name_map(&self.ctx);
        map.get(name).map(|&e| self.ctx.expr_index(e))
    }
}

#[pyfunction]
pub fn parse(path: &str) -> PyResult<Design> {
    // Robust path: avoid panics from parse_file_with_ctx File::open(...).expect(...)
    let contents = std::fs::read_to_string(path)
        .map_err(|e| PyIOError::new_err(format!("I/O error reading '{path}': {e}")))?;
    let mut ctx = Context::default();
    let name = std::path::Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str());
    match btor2::parse_str(&mut ctx, &contents, name) {
        Some(sys) => Ok(Design { ctx, sys }),
        None => Err(PyValueError::new_err(format!(
            "Parse failed for BTOR file: {path}"
        ))),
    }
}

#[pymodule]
fn patronus_btor(_py: Python<'_>, m: &pyo3::Bound<'_, pyo3::types::PyModule>) -> PyResult<()> {
    m.add_class::<Design>()?;
    m.add_function(wrap_pyfunction!(parse, m)?)?;
    Ok(())
}

// Helpers

fn expr_to_dict(py: Python<'_>, e: &Expr, ctx: &Context) -> PyResult<PyObject> {
    let d = pyo3::types::PyDict::new_bound(py);

    macro_rules! set {
        ($k:expr, $v:expr) => {
            d.set_item($k, $v)?
        };
    }
    macro_rules! idx {
        ($r:expr) => {
            ctx.expr_index($r)
        };
    }

    match e {
        // Bit-Vector Expressions
        Expr::BVSymbol { name, width } => {
            set!("kind", "BVSymbol");
            set!("name", ctx[*name].as_str());
            set!("width", *width as u64);
        }
        Expr::BVLiteral(v) => {
            set!("kind", "BVLiteral");
            let w = v.width();
            let value = v.get(ctx);
            // mimic serialize.rs formatting
            let s = if w <= 8 {
                format!("{}'b{}", w, value.to_bit_str())
            } else {
                format!("{}'x{}", w, value.to_hex_str())
            };
            set!("width", w as u64);
            set!("value", s);
            // Also expose numeric hex without width prefix for convenience
            set!("hex", value.to_hex_str());
        }
        // unary with explicit fields
        Expr::BVZeroExt { e, by, width } => {
            set!("kind", "BVZeroExt");
            set!("e", idx!(*e));
            set!("by", *by as u64);
            set!("width", *width as u64);
        }
        Expr::BVSignExt { e, by, width } => {
            set!("kind", "BVSignExt");
            set!("e", idx!(*e));
            set!("by", *by as u64);
            set!("width", *width as u64);
        }
        Expr::BVSlice { e, hi, lo } => {
            set!("kind", "BVSlice");
            set!("e", idx!(*e));
            set!("hi", *hi as u64);
            set!("lo", *lo as u64);
        }
        Expr::BVNot(e, width) => {
            set!("kind", "BVNot");
            set!("e", idx!(*e));
            set!("width", *width as u64);
        }
        Expr::BVNegate(e, width) => {
            set!("kind", "BVNegate");
            set!("e", idx!(*e));
            set!("width", *width as u64);
        }
        // binary logical/compare/arithmetic
        Expr::BVEqual(a, b) => {
            set!("kind", "BVEqual");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
        }
        Expr::BVImplies(a, b) => {
            set!("kind", "BVImplies");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
        }
        Expr::BVGreater(a, b) => {
            set!("kind", "BVGreater");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
        }
        Expr::BVGreaterSigned(a, b, width) => {
            set!("kind", "BVGreaterSigned");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVGreaterEqual(a, b) => {
            set!("kind", "BVGreaterEqual");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
        }
        Expr::BVGreaterEqualSigned(a, b, width) => {
            set!("kind", "BVGreaterEqualSigned");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVConcat(a, b, width) => {
            set!("kind", "BVConcat");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVAnd(a, b, width) => {
            set!("kind", "BVAnd");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVOr(a, b, width) => {
            set!("kind", "BVOr");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVXor(a, b, width) => {
            set!("kind", "BVXor");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVShiftLeft(a, b, width) => {
            set!("kind", "BVShiftLeft");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVArithmeticShiftRight(a, b, width) => {
            set!("kind", "BVArithmeticShiftRight");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVShiftRight(a, b, width) => {
            set!("kind", "BVShiftRight");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVAdd(a, b, width) => {
            set!("kind", "BVAdd");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVMul(a, b, width) => {
            set!("kind", "BVMul");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVSignedDiv(a, b, width) => {
            set!("kind", "BVSignedDiv");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVUnsignedDiv(a, b, width) => {
            set!("kind", "BVUnsignedDiv");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVSignedMod(a, b, width) => {
            set!("kind", "BVSignedMod");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVSignedRem(a, b, width) => {
            set!("kind", "BVSignedRem");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVUnsignedRem(a, b, width) => {
            set!("kind", "BVUnsignedRem");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVSub(a, b, width) => {
            set!("kind", "BVSub");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
            set!("width", *width as u64);
        }
        Expr::BVArrayRead { array, index, width } => {
            set!("kind", "BVArrayRead");
            set!("array", idx!(*array));
            set!("index", idx!(*index));
            set!("width", *width as u64);
        }
        Expr::BVIte { cond, tru, fals } => {
            set!("kind", "BVIte");
            set!("cond", idx!(*cond));
            set!("tru", idx!(*tru));
            set!("fals", idx!(*fals));
        }

        // Array Expressions
        Expr::ArraySymbol {
            name,
            index_width,
            data_width,
        } => {
            set!("kind", "ArraySymbol");
            set!("name", ctx[*name].as_str());
            set!("index_width", *index_width as u64);
            set!("data_width", *data_width as u64);
        }
        Expr::ArrayConstant {
            e,
            index_width,
            data_width,
        } => {
            set!("kind", "ArrayConstant");
            set!("e", idx!(*e));
            set!("index_width", *index_width as u64);
            set!("data_width", *data_width as u64);
        }
        Expr::ArrayEqual(a, b) => {
            set!("kind", "ArrayEqual");
            set!("a", idx!(*a));
            set!("b", idx!(*b));
        }
        Expr::ArrayStore { array, index, data } => {
            set!("kind", "ArrayStore");
            set!("array", idx!(*array));
            set!("index", idx!(*index));
            set!("data", idx!(*data));
        }
        Expr::ArrayIte { cond, tru, fals } => {
            set!("kind", "ArrayIte");
            set!("cond", idx!(*cond));
            set!("tru", idx!(*tru));
            set!("fals", idx!(*fals));
        }
    }

    Ok(d.into_py(py))
}
