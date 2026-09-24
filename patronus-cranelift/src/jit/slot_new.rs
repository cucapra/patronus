use baa::BitVecValue;
use patronus::expr::{self, TypeCheck};
use patronus::system;
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct StateBuf {
    offsets: FxHashMap<expr::ExprRef, usize>,
    data: Vec<u64>,
    types: Vec<expr::Type>,
}

// TODO: singleton ledger
impl StateBuf {
    pub fn init(&mut self, g: &mut patronus::sim::InitValueGenerator) {
        for (idx, slot) in &mut self.data.iter_mut().enumerate() {
            let init_value = g.generate(self.types[idx]);
            *slot = init_value.try_into_u64().unwrap();
        }
    }

    pub fn new_singleton(ctx: &expr::Context, expr: expr::ExprRef) -> Self {
        let mut offset_map = FxHashMap::default();
        offset_map.insert(expr, 0);
        Self {
            offsets: offset_map,
            data: vec![0],
            types: vec![expr.get_type(&ctx)],
        }
    }

    // for a subset of expressions
    pub fn new_exprset(
        ctx: &expr::Context,
        exprs: &Vec<expr::ExprRef>,
        offsets: FxHashMap<expr::ExprRef, usize>,
    ) -> Self {
        let mut assignment = FxHashMap::default();
        let dtypes: Vec<_> = exprs.iter().map(|&e| e.get_type(ctx)).collect();
        for &e in exprs.iter() {
            assert!(
                assignment
                    .insert(offsets.get(&e).expect("input expr not found"), 0)
                    .is_none(),
                "slot conflict, multiple data are assigned to the same slot"
            );
        }
        let slots: Vec<_> = (0..exprs.len())
            .map(|idx| {
                assignment
                    .remove(&idx)
                    .expect("slot assignment out of range")
            })
            .collect();

        StateBuf {
            offsets,
            data: slots,
            types: dtypes,
        }
    }

    pub fn new(ctx: &expr::Context, sys: &system::TransitionSystem) -> Self {
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
        Self::new_exprset(ctx, &exprs, offset_map)
    }

    pub fn swap(&mut self, other: &mut Self) {
        debug_assert!(self.types == other.types);
        std::mem::swap(&mut self.data, &mut other.data)
    }

    pub fn as_raw_data_slice(&self) -> &[u64] {
        self.data.as_slice()
    }

    pub fn as_mut_raw_data_slice(&mut self) -> &mut [u64] {
        self.data.as_mut_slice()
    }

    pub fn offset_query(&self, expr: expr::ExprRef) -> Option<usize> {
        self.offsets
            .get(&expr)
            .filter(|offset| **offset < self.data.len())
            .cloned()
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
