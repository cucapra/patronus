use super::ledger::*;

use patronus::expr::*;
use patronus::system::*;
use rustc_hash::FxHashMap;

/// The `StateBuffer` associates each `state` expression with an expr slot.
/// Its expr ledge routes each state's expr to slot offset.
pub struct StateBuffer {
    pub ledge: ExprLedge,
}

impl StateBuffer {
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

pub fn build_in_out_state_buffer(
    ctx: &Context,
    sys: &TransitionSystem,
) -> (StateBuffer, StateBuffer) {
    (StateBuffer::new(ctx, sys), StateBuffer::new(ctx, sys))
}

impl StateBuffer {
    fn new(ctx: &Context, sys: &TransitionSystem) -> Self {
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
            ledge: ExprLedge::new(ctx, &exprs, offset_map),
        }
    }

    pub fn get_state_offset(&self, symbol: ExprRef) -> usize {
        self.ledge
            .offset_query(symbol)
            .expect("queried symbol is not part of the state")
    }
}

impl Clone for StateBuffer {
    fn clone(&self) -> Self {
        let mut cloned_ledge = self.ledge.shallow_clone();
        for (mut dst, src) in (&mut cloned_ledge).into_iter().zip(&self.ledge) {
            dst.copy_from(src);
        }

        StateBuffer {
            ledge: cloned_ledge,
        }
    }
}
