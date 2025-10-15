use pyo3::prelude::*;

#[pyclass]
struct Simulator(Box<dyn ::patronus::sim::Simulator<>>);