// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use super::slot::*;
use baa::*;

pub(super) struct BaaValueConverter;
pub(super) struct BaaValueSetter<'a>(pub &'a baa::Value);

impl SlotDataRefReduce for BaaValueConverter {
    type Output = baa::Value;
    fn with_bit_vec(&mut self, data: &[u64], width: WidthInt) -> Self::Output {
        baa::Value::BitVec(BitVecValueRef::new(data, width).into())
    }
    fn with_primitive_array<T: Into<u64> + Copy>(
        &mut self,
        data: &[T],
        _: WidthInt,
        _: WidthInt,
    ) -> Self::Output {
        let words: Vec<u64> = Vec::from_iter(data.iter().map(|&v| v.into()));
        // XXX: this might be wrong
        baa::Value::Array(words.as_slice().into())
    }
}

impl SlotDataRefMutReduce for BaaValueSetter<'_> {
    type Output = ();
    fn with_bit_vec(&mut self, data: &mut [u64], _width: WidthInt) -> Self::Output {
        if let baa::Value::BitVec(bv) = self.0 {
            data.copy_from_slice(bv.words())
        } else {
            panic!("slot data type mismatch")
        }
    }
    fn with_primitive_array<T: TryFrom<u64>>(
        &mut self,
        data: &mut [T],
        index_width: WidthInt,
        _data_width: WidthInt,
    ) -> Self::Output {
        let baa::Value::Array(array) = self.0 else {
            panic!("slot data type mismatch")
        };
        data.iter_mut().enumerate().for_each(|(idx, v)| {
            let src = array.select(&BitVecValue::from_u64(idx as u64, index_width));
            *v =
                src.to_u64().unwrap().try_into().unwrap_or_else(|_| {
                    panic!("baa array element can not be converted to u64 safely")
                });
        });
    }
}
