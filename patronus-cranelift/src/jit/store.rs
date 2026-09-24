use super::slot_new::*;
use baa::{BitVecOps, BitVecValueRef};

use patronus::{
    expr::{self, *},
    system::TransitionSystem,
};

pub(crate) struct JITState {
    pub(crate) in_state: StateBuf,
    pub(crate) out_state: StateBuf,
}

impl JITState {
    pub(crate) fn new(ctx: &expr::Context, sys: &TransitionSystem) -> JITState {
        let in_state = StateBuf::new(ctx, sys);
        let out_state = in_state.clone();

        Self {
            in_state,
            out_state,
        }
    }

    pub(crate) fn gen_init(&mut self, g: &mut patronus::sim::InitValueGenerator) {
        self.in_state.init(g)
    }

    pub(crate) fn swap_states(&mut self) {
        self.in_state.swap(&mut self.out_state);
    }

    pub(crate) fn set<'a>(&mut self, expr: ExprRef, vref: BitVecValueRef<'a>) {
        let offset = self.in_state.offset_query(expr).unwrap();
        self.in_state.set_slot(offset, vref.words());
        self.out_state.set_slot(offset, vref.words());
    }
}
