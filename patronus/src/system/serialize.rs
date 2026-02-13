// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::TransitionSystem;
use super::analysis::{SerializeSignalKind, analyze_for_serialization};
use crate::expr::{
    Context, ExprRef, SerializableIrNode, SparseExprMap, TypeCheck, serialize_expr,
    serialize_expr_ref,
};
use std::io::Write;

fn serialize_transition_system<W: Write>(
    ctx: &Context,
    sys: &TransitionSystem,
    writer: &mut W,
) -> std::io::Result<()> {
    if !sys.name.is_empty() {
        writeln!(writer, "{}", sys.name)?;
    }

    let signals = analyze_for_serialization(ctx, sys, true).signal_order;
    let mut names: SparseExprMap<Option<String>> = SparseExprMap::default();
    for root in signals.iter() {
        let name = root.name.map(|n| ctx[n].to_string()).unwrap_or_else(|| {
            sys.names[root.expr]
                .map(|n| ctx[n].clone())
                .unwrap_or(format!("%{}", usize::from(root.expr)))
        });
        // outputs should not overwrite other names
        if root.kind != SerializeSignalKind::Output || names[root.expr].is_none() {
            names[root.expr] = Some(name);
        }
    }

    // this closure allows us to use node names instead of serializing all sub-expressions
    let serialize_child = |expr_ref: &ExprRef, writer: &mut W| -> std::io::Result<bool> {
        if let Some(name) = &names[*expr_ref] {
            write!(writer, "{}", name)?;
            Ok(false)
        } else {
            Ok(true) // recurse to child
        }
    };

    // signals
    for root in signals.iter() {
        let name = root
            .name
            .map(|n| &ctx[n])
            .unwrap_or_else(|| names[root.expr].as_ref().unwrap());
        let expr = &ctx[root.expr];

        // print the kind and name
        let kind = kind_to_string(root.kind);
        write!(writer, "{} {}", kind, name)?;

        // print the type
        let tpe = expr.get_type(ctx);
        write!(writer, " : {tpe}",)?;

        if expr.is_symbol() && expr.get_symbol_name(ctx).unwrap() == name {
            writeln!(writer)?;
        } else {
            write!(writer, " = ")?;
            serialize_expr(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
    }

    // states
    for state in sys.states.iter() {
        let name = ctx
            .get_symbol_name(state.symbol)
            .expect("all states are required to have a name!");
        let tpe = state.symbol.get_type(ctx);
        writeln!(writer, "state {name} : {tpe}")?;

        if let Some(expr) = &state.init {
            write!(writer, "  [init] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
        if let Some(expr) = &state.next {
            write!(writer, "  [next] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
    }

    Ok(())
}

fn kind_to_string(kind: SerializeSignalKind) -> &'static str {
    match kind {
        SerializeSignalKind::BadState => "bad",
        SerializeSignalKind::Constraint => "constraint",
        SerializeSignalKind::Output => "output",
        SerializeSignalKind::Input => "input",
        SerializeSignalKind::StateInit => "init",
        SerializeSignalKind::StateNext => "next",
        SerializeSignalKind::None => "node",
    }
}

impl SerializableIrNode for TransitionSystem {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        serialize_transition_system(ctx, self, writer)
    }
}
