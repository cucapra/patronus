from setuptools import setup
from setuptools_rust import Binding, RustExtension

setup(
    name="patronus-btor",
    version="0.1.0",
    description="PyO3 bindings for Patronus BTOR parsing",
    rust_extensions=[
        RustExtension(
            "patronus_btor",
            path="Cargo.toml",
            binding=Binding.PyO3,
        )
    ],
    zip_safe=False,
)
