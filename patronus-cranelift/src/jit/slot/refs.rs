use super::base::*;
use super::converter::*;
use patronus::expr::{self, *};

#[derive(PartialEq, Eq)]
pub struct SlotDataRef<'a> {
    kind: SlotDataRefKind<'a>,
    pub tpe: expr::Type,
}

pub struct SlotDataRefMut<'a> {
    kind: SlotDataRefMutKind<'a>,
    pub tpe: expr::Type,
}

#[derive(PartialEq, Eq)]
enum SlotDataRefKind<'a> {
    BitVec(&'a [u64]),
}

enum SlotDataRefMutKind<'a> {
    BitVec(&'a mut [u64]),
}

impl OpaqueSlotData {
    /// reinterpret as a bitvec: returns a pointer to this element as a bitvec
    fn as_bit_vec<'a>(&'a self, width: WidthInt) -> SlotDataRefKind<'a> {
        let words_slice = if width <= 64 {
            std::slice::from_ref(&self.0)
        } else {
            panic!("tried to deref a pointer to bitvec of excess width");
        };
        SlotDataRefKind::BitVec(words_slice)
    }

    /// reinterpret as a bitvec: points to owned memory
    fn as_bit_vec_mut<'a>(&'a mut self, width: WidthInt) -> SlotDataRefMutKind<'a> {
        let words_slice = if width <= 64 {
            std::slice::from_mut(&mut self.0)
        } else {
            panic!("tried to deref a pointer to bitvec of excess width");
        };
        SlotDataRefMutKind::BitVec(words_slice)
    }
}

impl<'a> SlotDataRef<'a> {
    pub(super) fn from_opaque_data<'slot>(
        data: &'slot OpaqueSlotData,
        tpe: expr::Type,
    ) -> SlotDataRef<'slot> {
        let kind = match tpe {
            expr::Type::BV(width) => data.as_bit_vec(width),
            _ => panic!("unimplemented type"),
        };
        SlotDataRef { kind, tpe }
    }

    /// get a owned clone of the data at the referenced location
    pub fn reduce<T>(&self, mut reducer: impl SlotDataRefReduce<Output = T>) -> T {
        match self.kind {
            SlotDataRefKind::BitVec(data) => {
                reducer.with_bit_vec(data, self.tpe.get_bit_vector_width().unwrap())
            }
        }
    }
}

impl<'a> SlotDataRefMut<'a> {
    pub(super) fn from_opaque_data<'slot>(
        data: &'slot mut OpaqueSlotData,
        tpe: expr::Type,
    ) -> SlotDataRefMut<'slot> {
        let kind = match tpe {
            expr::Type::BV(width) => data.as_bit_vec_mut(width),
            _ => panic!("unimplemented type"),
        };
        SlotDataRefMut { kind, tpe }
    }

    pub fn reduce<T>(&mut self, mut reducer: impl SlotDataRefMutReduce<Output = T>) -> T {
        match &mut self.kind {
            SlotDataRefMutKind::BitVec(data) => {
                reducer.with_bit_vec(data, self.tpe.get_bit_vector_width().unwrap())
            }
        }
    }

    pub fn expect_bit_vec(self) -> &'a mut [u64] {
        let SlotDataRefMutKind::BitVec(words) = self.kind;
        words
    }

    pub(super) fn copy_from(&mut self, other: SlotDataRef<'_>) {
        assert_eq!(self.tpe, other.tpe);
        match (&mut self.kind, other.kind) {
            (SlotDataRefMutKind::BitVec(dst), SlotDataRefKind::BitVec(src)) => {
                dst.copy_from_slice(src)
            }
        }
    }
}
