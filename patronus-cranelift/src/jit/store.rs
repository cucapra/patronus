use super::slot::*;
use baa::{BitVecOps, BitVecValueRef};
use fixedbitset::FixedBitSet;

use patronus::{
    expr::{self, *},
    system::TransitionSystem,
};
use rustc_hash::FxHashMap;

/// Minimum dirty percentage of output states that will trigger batched update mode
const BATCHED_UPDATE_THRESHOLD: f64 = 0.6;

// data storage structures

pub(crate) enum DirtyUpdatePolicy {
    Sparse,
    Batched,
}

pub(crate) struct DirtyStateRegistry {
    pub(crate) states: FixedBitSet,
    /// Currently used in `mark_dirty_states` to store the dirty states for next step to avoid heap allocation
    scratch_states: FixedBitSet,
    num_total_states: f64,
}

impl DirtyStateRegistry {
    pub(crate) fn new(init_states: FixedBitSet, num_total_states: usize) -> Self {
        Self {
            states: init_states.clone(),
            scratch_states: FixedBitSet::with_capacity(num_total_states),
            num_total_states: num_total_states as f64,
        }
    }

    #[inline]
    pub(crate) fn register(&mut self, dirty_states: &FixedBitSet) {
        self.states.union_with(dirty_states);
    }

    pub(crate) fn select_update_policy(&self) -> DirtyUpdatePolicy {
        if self.dirty_percentage() >= BATCHED_UPDATE_THRESHOLD {
            DirtyUpdatePolicy::Batched
        } else {
            DirtyUpdatePolicy::Sparse
        }
    }

    #[inline]
    fn dirty_percentage(&self) -> f64 {
        (self.states.count_ones(..) as f64) / self.num_total_states
    }

    pub(crate) fn swap(&mut self) {
        std::mem::swap(&mut self.states, &mut self.scratch_states);
    }

    pub(crate) fn shootdown(&mut self) {
        self.states.insert_range(..);
    }
}

pub(crate) struct JITState {
    pub(crate) in_state: StateBuffer,
    pub(crate) out_state: StateBuffer,

    /// Maintains set of states that need to be recomputed at next step
    pub(crate) dirty_registry: DirtyStateRegistry,
}

fn check_slot_dirtiness(a: SlotDataRef<'_>, b: SlotDataRef<'_>) -> bool {
    if matches!(a.tpe, expr::Type::BV(_)) {
        a.ne(&b)
    } else {
        // TODO: Currently for input array, compiler might steal the previous input array.
        // We always conservatively assume that array symbol is always dirty
        true
    }
}

impl JITState {
    pub(crate) fn new(ctx: &expr::Context, sys: &TransitionSystem) -> JITState {
        let (in_state, out_state) = build_in_out_state_buffer(ctx, sys);
        let num_mutable_states = sys.states.len();
        let mut init_states = FixedBitSet::with_capacity(num_mutable_states);
        init_states.insert_range(..);
        let dirty_registry = DirtyStateRegistry::new(init_states, num_mutable_states);

        Self {
            in_state,
            out_state,
            dirty_registry,
        }
    }

    pub(crate) fn gen_init(&mut self, g: &mut patronus::sim::InitValueGenerator) {
        for mut data in &mut self.in_state.ledge {
            let init_value = g.generate(data.tpe);
            data.reduce(BaaValueSetter(&init_value));
        }
    }

    /// Inspect current state and next state to find those that are modified in last `step` call;
    /// Schedule them to be re-computed at next `step` by adding them to `dirty_states`
    pub(crate) fn mark_dirty_states(
        &mut self,
        upstream_deps: &FxHashMap<ExprRef, FixedBitSet>,
        sys: &TransitionSystem,
    ) {
        let states_require_reexamine = &self.dirty_registry.states;
        let next_step_dirty_states = &mut self.dirty_registry.scratch_states;
        next_step_dirty_states.clear();
        // Correctness relies on the fact that mutable state is always put at the front of the slot
        for offset in states_require_reexamine.ones() {
            let current = self.in_state.ledge.get_slot_data_at_offset(offset);
            let next = self.out_state.ledge.get_slot_data_at_offset(offset);
            if check_slot_dirtiness(current, next)
                && let Some(roots) = upstream_deps.get(&sys.states[offset].symbol)
            {
                next_step_dirty_states.union_with(roots);
            }
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
