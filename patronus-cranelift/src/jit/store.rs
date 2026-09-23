use super::slot::*;
use baa::{BitVecOps, BitVecValueRef};
use fixedbitset::FixedBitSet;

use patronus::{
    expr::{self, *},
    system::TransitionSystem,
};

pub(crate) struct JITState {
    pub(crate) in_state: StateBuffer,
    pub(crate) out_state: StateBuffer,
}

impl JITState {
    pub(crate) fn new(ctx: &expr::Context, sys: &TransitionSystem) -> JITState {
        let (in_state, out_state) = build_in_out_state_buffer(ctx, sys);
        let num_mutable_states = sys.states.len();
        let mut init_states = FixedBitSet::with_capacity(num_mutable_states);
        init_states.insert_range(..);

        Self {
            in_state,
            out_state,
        }
    }

    pub(crate) fn gen_init(&mut self, g: &mut patronus::sim::InitValueGenerator) {
        for mut data in &mut self.in_state.ledge {
            let init_value = g.generate(data.tpe);
            data.reduce(BaaValueSetter(&init_value));
        }
    }

    pub(crate) fn swap_states(&mut self) {
        // SAFETY: input and output state buffer are guaranteed to contain the same slot layout
        unsafe {
            self.in_state.swap(&mut self.out_state);
        }
    }

    pub(crate) fn in_ledge(&self) -> &ExprLedge {
        &self.in_state.ledge
    }

    pub(crate) fn set<'a>(&mut self, expr: ExprRef, vref: BitVecValueRef<'a>) {
        self.in_state
            .ledge
            .get_slot_data_mut(expr)
            .unwrap()
            .expect_bit_vec()
            .copy_from_slice(vref.words());
        self.out_state
            .ledge
            .get_slot_data_mut(expr)
            .unwrap()
            .expect_bit_vec()
            .copy_from_slice(vref.words());
    }
}
