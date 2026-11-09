// Copyright 2026 Cornell University
// released under BSD 3-Clause License
// author: Willow Ge <lg634@cornell.edu>

use baa::{BitVecOps, BitVecValue, BitVecValueRef};
use patronus::expr::{self, TypeCheck};
use rustc_hash::FxHashMap;

#[derive(Clone, Debug, Default)]
pub struct StateBuf {
    offsets: FxHashMap<expr::ExprRef, usize>,
    data: Vec<u64>,
    types: Vec<expr::Type>,
}

pub(crate) fn calc_words<const WORD_WIDTH: usize>(in_width: u32) -> usize {
    if (in_width as usize) % WORD_WIDTH == 0 {
        (in_width as usize) / WORD_WIDTH
    } else {
        (in_width as usize) / WORD_WIDTH + 1
    }
}

pub(crate) fn words_in_ty<const WORD_WIDTH: usize>(tref: &expr::Type) -> usize {
    if tref.is_bit_vector() {
        calc_words::<WORD_WIDTH>(tref.get_bit_vector_width().unwrap())
    } else {
        panic!("can't compute words in arrays yet")
    }
}

impl StateBuf {
    pub fn add_exprs(&mut self, ctx: &expr::Context, exprs: &Vec<expr::ExprRef>) {
        let new_dtypes: Vec<_> = exprs.iter().map(|&e| e.get_type(ctx)).collect();
        let new_size: usize = new_dtypes.iter().map(|t| words_in_ty::<64>(t)).sum();
        // data is zero initialised
        let new_data = vec![0; new_size];
        let start_len = self.data.len();
        let mut offset_acc = 0;
        for eref in exprs.iter() {
            self.offsets.insert(*eref, start_len + offset_acc);
            offset_acc += calc_words::<64>(eref.get_bv_type(ctx).unwrap());
        }
        self.data.extend(new_data);
        self.types.extend(new_dtypes);
    }

    pub fn init(&mut self, g: &mut patronus::sim::InitValueGenerator) {
        let mut offset = 0;
        for i in 0..self.types.len() {
            let init_value = g.generate(self.types[i]);
            match init_value {
                baa::Value::Array(..) => panic!("arrays unsupported"),
                baa::Value::BitVec(v) => self.set_slot(offset, v.words()),
            };
            offset += words_in_ty::<64>(&self.types[i]);
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
        // let num_words = words_in_ty(self.types[offset])

        //     calc_words::<64>(self.types[offset].get_bit_vector_width().unwrap());
        // debug_assert_eq!(num_words, data.len());
        // println!("{}", data.len());
        let assoc_pos = self.data.get_mut(offset..(offset + data.len())).unwrap();
        assoc_pos.clone_from_slice(data);
    }

    pub fn get_slot(&self, expr: expr::ExprRef) -> BitVecValue {
        let offset = self.offset_query(expr).unwrap();
        let dtype = self.types[offset];
        let sl = self
            .data
            .get(offset..(offset + words_in_ty::<64>(&dtype)))
            .unwrap();
        let slot_ref = BitVecValueRef::new(sl, dtype.get_bit_vector_width().unwrap());
        BitVecValue::from(slot_ref)
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
