// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::expr::{ArrayType, ExprRef, Type};
use baa::{ArrayValue, BitVecValue, BitVecValueRef, Value};
use rand::SeedableRng;
use rand::rngs::SmallRng;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum InitKind {
    Zero,
    Random(u64),
}

/// An implementation of a transition system simulator.
pub trait Simulator {
    type SnapshotId;

    /// Initializes all states and inputs to zero.
    fn init(&mut self, kind: InitKind);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value or an expression in the simulator.
    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>);

    /// Inspect the value of any expression in the circuit
    fn get(&self, expr: ExprRef) -> Value;

    fn step_count(&self) -> u64;

    /// Takes a snapshot of the state (excluding inputs) and saves it internally.
    fn take_snapshot(&mut self) -> Self::SnapshotId;
    /// Restores a snapshot that was previously taken with the same simulator.
    fn restore_snapshot(&mut self, id: Self::SnapshotId);
}

pub struct InitValueGenerator {
    rng: Option<SmallRng>,
}

impl InitValueGenerator {
    pub fn from_kind(kind: InitKind) -> Self {
        match kind {
            InitKind::Zero => Self { rng: None },
            InitKind::Random(seed) => Self {
                rng: Some(SmallRng::seed_from_u64(seed)),
            },
        }
    }

    pub fn generate(&mut self, tpe: Type) -> Value {
        match tpe {
            Type::BV(bits) => {
                if let Some(rng) = &mut self.rng {
                    BitVecValue::random(rng, bits).into()
                } else {
                    BitVecValue::zero(bits).into()
                }
            }
            Type::Array(ArrayType {
                index_width,
                data_width,
            }) => {
                if let Some(rng) = &mut self.rng {
                    ArrayValue::random(rng, index_width, data_width).into()
                } else {
                    ArrayValue::new_sparse(index_width, &BitVecValue::zero(data_width)).into()
                }
            }
        }
    }
}
