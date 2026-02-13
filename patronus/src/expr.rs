// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod analysis;
mod context;
mod eval;
mod foreach;
mod meta;
mod nodes;
mod parse;
mod serialize;
mod simplify;
mod transform;
pub mod traversal;
mod types;

pub use analysis::{UseCountInt, count_expr_uses, find_symbols, update_expr_child_uses};
pub use context::{Builder, Context, ExprRef, StringRef};
pub use eval::{SymbolValueStore, eval_array_expr, eval_bv_expr, eval_expr};
pub use foreach::ForEachChild;
pub use meta::{
    DenseExprMetaData, DenseExprSet, ExprMap, ExprSet, SparseExprMap, SparseExprSet,
    get_fixed_point,
};
pub use nodes::{ArrayType, BVLitValue, Expr, Type, WidthInt};
pub use parse::parse_expr;
pub use serialize::SerializableIrNode;
pub(crate) use serialize::{serialize_expr, serialize_expr_ref};
pub(crate) use simplify::simplify;
pub use simplify::{Simplifier, simplify_single_expression};
pub use transform::simple_transform_expr;
pub(crate) use transform::{ExprTransformMode, do_transform_expr};
pub use types::{TypeCheck, TypeCheckError};
