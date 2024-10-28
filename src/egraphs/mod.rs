// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
mod arithmetic;
use crate::ir;
use baa::WidthInt;
use egg::{rewrite, Id, Language};

/// Shadow version of our `[crate::ir::Expr]` that abides by the `egg` rules.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum Expr {
    BVSymbol {
        name: ir::StringRef,
        width: WidthInt,
    },
    // TODO
    BVNot([Id; 1], WidthInt),
}

impl egg::Language for Expr {
    fn matches(&self, other: &Self) -> bool {
        // quick check to ensure that we are comparing the same kind of expression
        if std::mem::discriminant(self) != std::mem::discriminant(other) {
            return false;
        }
        // special comparisons for additional attributes
        match (self, other) {
            (Expr::BVNot(_, w0), Expr::BVNot(_, w1)) => w0 == w1,
            (_, _) => true,
        }
    }

    fn children(&self) -> &[Id] {
        match self {
            Expr::BVNot(cc, _) => cc,
            _ => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Expr::BVNot(cc, _) => cc,
            _ => &mut [],
        }
    }
}

impl egg::FromOp for Expr {
    type Error = ();

    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        match op {
            "not" => Ok(Expr::BVNot([children[0]], 1)),
            _ => Err(()),
        }
    }
}

/// Convert from our internal representation to the shadow version suitable for egg.
fn to_egg(ctx: &ir::Context, e: ir::ExprRef) -> egg::RecExpr<Expr> {
    let mut out = egg::RecExpr::default();
    ir::traversal::bottom_up(ctx, e, |_ctx, expr, children| match *expr {
        ir::Expr::BVSymbol { name, width } => out.add(Expr::BVSymbol { name, width }),
        ir::Expr::BVNot(_, width) => out.add(Expr::BVNot([children[0]], width)),
        _ => todo!(),
    });
    out
}

fn from_egg(ctx: &mut ir::Context, expr: &egg::RecExpr<Expr>) -> ir::ExprRef {
    let expressions = expr.as_ref();
    let mut todo = vec![(expressions.len() - 1, false)];
    let mut stack = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = &expressions[e];

        // Check if there are children that we need to compute first.
        if !bottom_up && !expr.children().is_empty() {
            todo.push((e, true));
            for child_id in expr.children() {
                todo.push((usize::from(*child_id), false));
            }
            continue;
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let result = match expr {
            Expr::BVSymbol { name, width } => ctx.symbol(*name, ir::Type::BV(*width)),
            Expr::BVNot(_, _) => ctx.not(stack.pop().unwrap()),
        };
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn basic_rewrites() -> Vec<egg::Rewrite<Expr, ()>> {
        vec![rewrite!("not-not"; "(not (not ?a))" => "?a")]
    }

    #[test]
    fn test_not_not() {
        let mut ctx = ir::Context::default();
        let a = ctx.bv_symbol("a", 1);
        let not_not_a = ctx.build(|c| c.not(c.not(a)));
        let egg_expr_in = to_egg(&ctx, not_not_a);
        let runner = egg::Runner::default()
            .with_expr(&egg_expr_in)
            .run(&basic_rewrites());
        let root = runner.roots[0];
        let extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);
        let (best_cost, egg_expr_out) = extractor.find_best(root);

        // this conversion is not implemented yet, however, if we print out the egg expression,
        // we see that the result is in fact the expected `a`
        let simplified = from_egg(&mut ctx, &egg_expr_out);
        assert_eq!(simplified, a);
        assert_eq!(best_cost, 1);
    }
}
