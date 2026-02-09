// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use super::{State, TransitionSystem};
use crate::expr::*;
use rustc_hash::FxHashSet;

pub fn count_system_expr_uses(ctx: &Context, sys: &TransitionSystem) -> Vec<UseCountInt> {
    internal_count_expr_uses(ctx, sys, false)
}

fn internal_count_expr_uses(
    ctx: &Context,
    sys: &TransitionSystem,
    ignore_init: bool,
) -> Vec<UseCountInt> {
    let mut use_count: DenseExprMetaData<UseCountInt> = DenseExprMetaData::default();
    let states = sys.state_map();
    // all observable outputs are our roots
    let mut todo = sys.get_assert_assume_output_exprs();
    // ensure that all roots start with count 1
    for expr in todo.iter() {
        use_count[*expr] = 1;
    }

    while let Some(expr) = todo.pop() {
        if let Some(state) = states.get(&expr) {
            // for states, we also want to mark the initial and the next expression as used
            if let Some(init) = state.init {
                if !ignore_init {
                    let count = use_count[init];
                    if count == 0 {
                        use_count[init] = 1;
                        todo.push(init);
                    }
                }
            }
            if let Some(next) = state.next {
                let count = use_count[next];
                if count == 0 {
                    use_count[next] = 1;
                    todo.push(next);
                }
            }
        }

        update_expr_child_uses(ctx, expr, &mut use_count, &mut todo);
    }

    use_count.into_vec()
}

/// Generates a list of all inputs and states that can influence the `root` expression.
pub fn cone_of_influence(ctx: &Context, sys: &TransitionSystem, root: ExprRef) -> Vec<ExprRef> {
    // we need to follow next and init expressions for all states
    cone_of_influence_impl(ctx, sys, root, true, true)
}

/// Generates a list of all inputs and states that can influence the `root` expression, while the system is being initialized.
pub fn cone_of_influence_init(
    ctx: &Context,
    sys: &TransitionSystem,
    root: ExprRef,
) -> Vec<ExprRef> {
    cone_of_influence_impl(ctx, sys, root, false, true)
}

/// Generates a list of all inputs and states that can influence the `root` expression, combinationally.
pub fn cone_of_influence_comb(
    ctx: &Context,
    sys: &TransitionSystem,
    root: ExprRef,
) -> Vec<ExprRef> {
    cone_of_influence_impl(ctx, sys, root, false, false)
}

/// Internal implementation which allows us to define how we follow states.
fn cone_of_influence_impl(
    ctx: &Context,
    sys: &TransitionSystem,
    root: ExprRef,
    follow_next: bool,
    follow_init: bool,
) -> Vec<ExprRef> {
    let mut out = vec![];
    let mut todo = vec![root];
    let mut visited = DenseExprSet::default();
    let states = sys.state_map();
    let inputs = sys.input_set();

    while let Some(expr_ref) = todo.pop() {
        if visited.contains(&expr_ref) {
            continue;
        }

        // make sure children are visited
        let expr = &ctx[expr_ref];
        expr.for_each_child(|c| {
            if !visited.contains(c) {
                todo.push(*c);
            }
        });

        // for states, we might want to follow the next and init expressions
        if let Some(state) = states.get(&expr_ref) {
            if follow_init {
                if let Some(c) = state.init {
                    if !visited.contains(&c) {
                        todo.push(c);
                    }
                }
            }
            if follow_next {
                if let Some(c) = state.next {
                    if !visited.contains(&c) {
                        todo.push(c);
                    }
                }
            }
        }

        // check to see if this is a state or input
        if expr.is_symbol() && (states.contains_key(&expr_ref) || inputs.contains(&expr_ref)) {
            out.push(expr_ref);
        }
        visited.insert(expr_ref);
    }

    out
}

#[derive(Debug, Clone)]
pub struct RootInfo {
    pub expr: ExprRef,
    pub name: Option<StringRef>,
    pub uses: Uses,
    pub kind: SerializeSignalKind,
}

impl RootInfo {
    fn new(expr: ExprRef, name: Option<StringRef>, uses: Uses, kind: SerializeSignalKind) -> Self {
        Self {
            expr,
            name,
            uses,
            kind,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SerializeSignalKind {
    BadState,
    Constraint,
    Output,
    Input,
    StateInit,
    StateNext,
    None,
}

/// Indicates which context an expression is used in.
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct Uses {
    pub next: UseCountInt,
    pub init: UseCountInt,
    pub other: UseCountInt,
}

impl Uses {
    #[inline]
    pub fn is_used(&self) -> bool {
        self.total() > 0
    }
    #[inline]
    pub fn total(&self) -> UseCountInt {
        self.next
            .saturating_add(self.init)
            .saturating_add(self.other)
    }
}

/// analyzes expression uses to determine in what contexts the expression is used.
fn determine_simples_uses(
    ctx: &Context,
    sys: &TransitionSystem,
    include_output: bool,
) -> impl ExprMap<Uses> {
    let init = count_expr_uses(ctx, sys.get_init_exprs());
    let next = count_expr_uses(ctx, sys.get_next_exprs());
    let other = if include_output {
        count_expr_uses(ctx, sys.get_assert_assume_output_exprs())
    } else {
        count_expr_uses(ctx, sys.get_assert_assume_exprs())
    };

    // collect all expressions
    let mut all_expr = FxHashSet::from_iter(other.non_default_value_keys());
    all_expr.extend(init.non_default_value_keys());
    all_expr.extend(next.non_default_value_keys());

    // generate combined map
    let mut out = SparseExprMap::default();
    for expr in all_expr.into_iter() {
        out[expr] = Uses {
            next: next[expr],
            init: init[expr],
            other: other[expr],
        };
    }
    out
}

/// Meta-data that helps with serialization, no matter if serializing to btor, our custom
/// "human-readable" format or SMTLib.
#[derive(Debug, Default, Clone)]
pub struct SerializeMeta {
    pub signal_order: Vec<RootInfo>,
}

pub fn analyze_for_serialization(
    ctx: &Context,
    sys: &TransitionSystem,
    include_outputs: bool,
) -> SerializeMeta {
    let uses = determine_simples_uses(ctx, sys, include_outputs);

    // always add all inputs first to the signal order
    let mut signal_order = Vec::new();
    for &input in sys.inputs.iter() {
        signal_order.push(RootInfo::new(
            input,
            Some(ctx[input].get_symbol_name_ref().unwrap()),
            uses[input],
            SerializeSignalKind::Input,
        ));
    }

    // keep track of which signals have been processed
    let mut visited = DenseExprSet::default();

    // add all roots and give them a large other count
    let mut todo: Vec<RootInfo> = vec![];
    if include_outputs {
        todo.extend(sys.outputs.iter().map(|o| {
            RootInfo::new(
                o.expr,
                Some(o.name),
                uses[o.expr],
                SerializeSignalKind::Output,
            )
        }));
    }
    todo.extend(sys.constraints.iter().map(|&e| {
        RootInfo::new(
            e,
            find_name(ctx, sys, e),
            uses[e],
            SerializeSignalKind::Constraint,
        )
    }));
    todo.extend(sys.bad_states.iter().map(|&e| {
        RootInfo::new(
            e,
            find_name(ctx, sys, e),
            uses[e],
            SerializeSignalKind::BadState,
        )
    }));

    // add state root expressions
    todo.extend(sys.get_init_exprs().iter().map(|&e| {
        RootInfo::new(
            e,
            find_name(ctx, sys, e),
            uses[e],
            SerializeSignalKind::StateInit,
        )
    }));
    todo.extend(sys.get_next_exprs().iter().map(|&e| {
        RootInfo::new(
            e,
            find_name(ctx, sys, e),
            uses[e],
            SerializeSignalKind::StateNext,
        )
    }));

    // visit roots in the order in which they were declared
    todo.reverse();

    // visit expressions
    while let Some(info) = todo.pop() {
        if visited.contains(&info.expr) {
            continue;
        }

        let expr = &ctx[info.expr];

        // check to see if all children are done
        let mut all_done = true;
        let mut num_children = 0;
        expr.for_each_child(|c| {
            if !visited.contains(c) {
                if all_done {
                    todo.push(info.clone()); // return expression to the todo list
                }
                all_done = false;
                // we need to visit the child first
                let child_info = RootInfo::new(*c, None, uses[*c], SerializeSignalKind::None);
                todo.push(child_info);
            }
            num_children += 1;
        });

        if !all_done {
            continue;
        }

        // add to signal order if applicable
        let is_output_like = matches!(
            info.kind,
            SerializeSignalKind::Output
                | SerializeSignalKind::Constraint
                | SerializeSignalKind::BadState
        );
        let is_input = info.kind == SerializeSignalKind::Input;
        if num_children > 0 || is_output_like || is_input {
            let used_multiple_times = info.uses.total() > 1;
            if is_output_like || used_multiple_times {
                signal_order.push(info.clone());
            }
        }
        visited.insert(info.expr);
    }

    SerializeMeta { signal_order }
}

#[inline]
fn find_name(ctx: &Context, sys: &TransitionSystem, e: ExprRef) -> Option<StringRef> {
    ctx[e].get_symbol_name_ref().or_else(|| sys.names[e])
}

impl ForEachChild<ExprRef> for State {
    fn for_each_child(&self, mut visitor: impl FnMut(&ExprRef)) {
        if let Some(next) = &self.next {
            visitor(next);
        }
        if let Some(init) = &self.init {
            visitor(init);
        }
    }

    fn num_children(&self) -> usize {
        self.next.is_some() as usize + self.init.is_some() as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::btor2;

    fn format_symbol_list(ctx: &Context, symbols: &[ExprRef]) -> String {
        let v: Vec<_> = symbols
            .iter()
            .map(|s| ctx.get_symbol_name(*s).unwrap())
            .collect();
        v.join(", ")
    }

    #[test]
    fn test_cone_of_influence() {
        let (ctx, sys) = btor2::parse_file("../inputs/unittest/delay.btor").unwrap();
        let reg0 = sys.get_state_by_name(&ctx, "reg0").unwrap().symbol;
        let reg1 = sys.get_state_by_name(&ctx, "reg1").unwrap().symbol;
        let cone0 = cone_of_influence(&ctx, &sys, reg0);
        let cone1 = cone_of_influence(&ctx, &sys, reg1);
        insta::assert_snapshot!(format_symbol_list(&ctx, &cone0));
        insta::assert_snapshot!(format_symbol_list(&ctx, &cone1));
        let cone2 = cone_of_influence_init(&ctx, &sys, reg0);
        assert_eq!(cone2, [reg0], "reg0 is initialized to zero. {:?}", cone2);
        let cone3 = cone_of_influence_init(&ctx, &sys, reg1);
        assert_eq!(cone3, [reg1], "reg1 is initialized to zero. {:?}", cone3);
    }
}
