// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Willow Ge <lg634@cornell.edu>

use std::cell::Ref;

use baa::BitVecValue;
use patronus::expr::{self, TypeCheck};
use rustc_hash::FxHashMap;

#[derive(Clone, Debug, Default)]
pub struct StateBuf {
    offsets: FxHashMap<expr::ExprRef, usize>,
    data: Vec<u64>,
    types: Vec<expr::Type>,
}

impl StateBuf {
    pub fn add_exprs(&mut self, ctx: &expr::Context, exprs: &Vec<expr::ExprRef>) {
        // data is zero initialised
        let new_data = vec![0; exprs.len()];
        let new_dtypes: Vec<_> = exprs.iter().map(|&e| e.get_type(ctx)).collect();
        let start_len = self.data.len();
        for (i, eref) in exprs.iter().enumerate() {
            self.offsets.insert(*eref, start_len + i);
        }
        self.data.extend(new_data);
        self.types.extend(new_dtypes);
    }

    pub fn init(&mut self, g: &mut patronus::sim::InitValueGenerator) {
        for (idx, slot) in &mut self.data.iter_mut().enumerate() {
            let init_value = g.generate(self.types[idx]);
            *slot = init_value.try_into_u64().unwrap();
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [u64] {
        self.data.as_mut_slice()
    }

    pub fn offset_query(&self, expr: expr::ExprRef) -> Option<usize> {
        self.offsets
            .get(&expr)
            .filter(|offset| **offset < self.data.len())
            .cloned()
    }

    pub fn batch_offsets(&self, batch: &[expr::ExprRef]) -> Vec<usize> {
        Vec::from_iter(batch.iter().map(|&sym| self.offset_query(sym).unwrap()))
    }

    pub fn contains(&self, expr: expr::ExprRef) -> bool {
        self.offsets.get(&expr).is_some()
    }

    pub fn set_slot(&mut self, offset: usize, data: &[u64]) {
        self.data[offset] = data[0];
    }

    pub fn get_slot(&self, expr: expr::ExprRef) -> BitVecValue {
        let offset = self.offset_query(expr).unwrap();
        let dtype = self.types[offset];
        BitVecValue::from_u64(self.data[offset], dtype.get_bit_vector_width().unwrap())
    }
}

impl patronus::expr::GetExprValue for StateBuf {
    fn get_bv(&self, _ctx: &expr::Context, symbol: expr::ExprRef) -> Option<BitVecValue> {
        if self.contains(symbol) {
            return Some(self.get_slot(symbol));
        }
        None
    }
    fn get_array(&self, _ctx: &expr::Context, _symbol: expr::ExprRef) -> Option<baa::ArrayValue> {
        panic!("arrays are unsupported")
    }
}
