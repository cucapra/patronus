use super::iter::*;

use patronus::expr::*;
use patronus::system::*;
use rustc_hash::FxHashMap;

/// The `StateBuffer` associates each `state` expression with an expr slot.
/// Its expr ledge routes each state's expr to slot offset.
pub struct StateBuffer<'expr> {
    pub ledge: ExprLedge,
    pub ctx: &'expr Context,
    pub sys: &'expr TransitionSystem,
}

impl StateBuffer<'_> {
    // SAFETY: caller should guarantee that each slot in `self` and `other` contains the same data type
    pub unsafe fn swap(&mut self, other: &mut Self) {
        debug_assert!(
            self.ledge
                .dtypes
                .iter()
                .zip(&other.ledge.dtypes)
                .all(|(a, b)| a.eq(b))
        );
        std::mem::swap(&mut self.ledge.slots, &mut other.ledge.slots);
    }
}

pub fn build_in_out_state_buffer<'a>(
    ctx: &'a Context,
    sys: &'a TransitionSystem,
) -> (StateBuffer<'a>, StateBuffer<'a>) {
    (StateBuffer::new(ctx, sys), StateBuffer::new(ctx, sys))
}

impl<'expr> StateBuffer<'expr> {
    fn new(ctx: &'expr Context, sys: &'expr TransitionSystem) -> Self {
        let mut offset_map = FxHashMap::default();
        let mut exprs = vec![];
        for (idx, &e) in sys
            .states
            .iter()
            .map(|s| &s.symbol)
            .chain(&sys.inputs)
            .enumerate()
        {
            offset_map.insert(e, idx);
            exprs.push(e);
        }
        Self {
            ledge: ExprLedge::new(ctx, &exprs, move |e| offset_map.get(&e).copied()),
            ctx,
            sys,
        }
    }

    pub fn get_state_offset(&self, symbol: ExprRef) -> usize {
        self.ledge
            .offset_query(symbol)
            .expect("queried symbol is not part of the state")
    }
}

impl Clone for StateBuffer<'_> {
    fn clone(&self) -> Self {
        let mut cloned_buffer = StateBuffer::new(self.ctx, self.sys);
        for (mut dst, src) in (&mut cloned_buffer.ledge).into_iter().zip(&self.ledge) {
            dst.copy_from(src);
        }
        cloned_buffer
    }
}
