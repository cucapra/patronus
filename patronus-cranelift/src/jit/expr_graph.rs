use patronus::expr::{traversal, *};
use rustc_hash::FxHashMap;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque, hash_map};

pub(crate) struct BottomUpExprGraph {
    pub(crate) roots: Vec<ExprRef>,
    /// For each expression node, tracks other nodes that directly depend on it
    pub(crate) node_dependents: FxHashMap<ExprRef, Vec<ExprRef>>,
}

impl BottomUpExprGraph {
    pub(crate) fn from_top_down_graph(ctx: &Context, top_down_roots: &[ExprRef]) -> Self {
        let mut bottom_up_roots = vec![];
        let mut node_dependents: FxHashMap<ExprRef, Vec<ExprRef>> =
            top_down_roots.iter().map(|&root| (root, vec![])).collect();

        traversal::top_down_without_reentry(ctx, top_down_roots, |ctx, current| {
            let mut has_children = false;
            ctx[current].for_each_child(|&child| {
                has_children = true;
                node_dependents.entry(child).or_default().push(current);
            });
            if !has_children {
                bottom_up_roots.push(current);
            }
            traversal::TraversalCmd::Continue
        });
        Self {
            roots: bottom_up_roots,
            node_dependents,
        }
    }

    /// Returns the default walker.
    /// There is no guarantee on the traversal order when multiple candidates are present.
    #[expect(dead_code)]
    pub(crate) fn walker(&self) -> BottomUpExprGraphWalker<'_> {
        BottomUpExprGraphWalker::new(self)
    }

    /// Returns a walker with custom candidate priority comparator.
    /// The internal representation is of candidates is a min-heap. Smaller value returned from `compare` will be prioritized.
    pub(crate) fn walker_with_sorted_fringe<'a, F>(
        &'a self,
        compare: &'a F,
    ) -> BiasedBottomUpExprGraphWalker<'a, F>
    where
        for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> std::cmp::Ordering,
    {
        BiasedBottomUpExprGraphWalker::new(self, compare)
    }

    fn node_in_degree(&self) -> FxHashMap<ExprRef, usize> {
        let mut in_degree: FxHashMap<ExprRef, usize> =
            self.roots.iter().map(|&expr| (expr, 0)).collect();
        for &dependent in self
            .node_dependents
            .iter()
            .flat_map(|(_, dependents)| dependents)
        {
            *in_degree.entry(dependent).or_default() += 1;
        }
        in_degree
    }
}

pub(crate) struct BottomUpExprGraphWalker<'a> {
    todo: VecDeque<ExprRef>,
    graph: &'a BottomUpExprGraph,
    in_degree: FxHashMap<ExprRef, usize>,
}

impl<'a> BottomUpExprGraphWalker<'a> {
    fn new(graph: &'a BottomUpExprGraph) -> Self {
        let mut in_degree = graph.node_in_degree();
        let todo = in_degree
            .extract_if(|_, &mut degree| degree == 0)
            .map(|(expr, _)| expr)
            .collect();
        Self {
            todo,
            graph,
            in_degree,
        }
    }
}

impl Iterator for BottomUpExprGraphWalker<'_> {
    type Item = ExprRef;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.todo.pop_front()?;
        for &dependent in &self.graph.node_dependents[&next] {
            let hash_map::Entry::Occupied(mut entry) = self.in_degree.entry(dependent) else {
                unreachable!()
            };
            let node_in_degree = entry.get_mut();
            *node_in_degree -= 1;
            if *node_in_degree == 0 {
                self.todo.push_back(dependent);
                entry.remove();
            }
        }
        Some(next)
    }
}

struct WeightedExprNode<'a, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    expr: ExprRef,
    compare: &'a F,
}

pub(crate) struct BiasedBottomUpExprGraphWalker<'a, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    todo: BinaryHeap<WeightedExprNode<'a, F>>,
    graph: &'a BottomUpExprGraph,
    in_degree: FxHashMap<ExprRef, usize>,
    fringe_compare: &'a F,
}

impl<'a, F> BiasedBottomUpExprGraphWalker<'a, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    fn new(graph: &'a BottomUpExprGraph, fringe_compare: &'a F) -> Self {
        let mut in_degree = graph.node_in_degree();
        let todo = in_degree
            .extract_if(|_, &mut degree| degree == 0)
            .map(|(expr, _)| WeightedExprNode {
                expr,
                compare: fringe_compare,
            })
            .collect();
        Self {
            todo,
            graph,
            in_degree,
            fringe_compare,
        }
    }
}

impl<'a, F> Iterator for BiasedBottomUpExprGraphWalker<'a, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    type Item = ExprRef;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.todo.pop()?;
        for &dependent in &self.graph.node_dependents[&next.expr] {
            let hash_map::Entry::Occupied(mut entry) = self.in_degree.entry(dependent) else {
                unreachable!()
            };
            let node_in_degree = entry.get_mut();
            *node_in_degree -= 1;
            if *node_in_degree == 0 {
                self.todo.push(WeightedExprNode {
                    expr: dependent,
                    compare: self.fringe_compare,
                });
                entry.remove();
            }
        }
        Some(next.expr)
    }
}

impl<F> std::cmp::Ord for WeightedExprNode<'_, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.compare)(&self.expr, &other.expr).reverse()
    }
}

impl<F> std::cmp::PartialOrd for WeightedExprNode<'_, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F> std::cmp::PartialEq for WeightedExprNode<'_, F>
where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering,
{
    fn eq(&self, other: &Self) -> bool {
        (self.compare)(&self.expr, &other.expr).is_eq()
    }
}

impl<F> std::cmp::Eq for WeightedExprNode<'_, F> where
    for<'e> F: Fn(&'e ExprRef, &'e ExprRef) -> Ordering
{
}
