use crate::jit::runtime;
use patronus::expr::{self, *};

use super::refs::*;

/// a word-width value-like 'thing'
#[repr(transparent)]
pub struct OpaqueSlotData(pub(super) u64);

impl OpaqueSlotData {
    /// create a new OpaqueSlotData based on ``tpe``.
    /// if ``tpe`` is a bitvec narrower than 64, the value should be interpreted as the bitvec value
    /// otherwise, it is the pointer to an array
    pub(super) fn new(tpe: expr::Type) -> Self {
        let raw = match tpe {
            expr::Type::BV(width) => {
                if width <= 64 {
                    0
                } else {
                    panic!("attempting to create slot of size >64b");
                }
            }
            expr::Type::Array(ArrayType {
                index_width,
                data_width,
            }) => {
                let (index_width, data_width) = (index_width as u64, data_width as u64);
                if data_width <= 64 {
                    runtime::__alloc_array(0, index_width, data_width) as u64
                } else {
                    panic!("attempting to create slot of array with element size >64b");
                }
            }
        };
        Self(raw)
    }
}

/// contains an immutable reference to some opaque data, and a type
pub struct SlotData {
    raw: OpaqueSlotData,
    tpe: expr::Type,
}

impl SlotData {
    /// get an immutable reference to the data pointed to by this slot
    pub fn as_ref(&self) -> SlotDataRef<'_> {
        SlotDataRef::from_opaque_data(&self.raw, self.tpe)
    }

    // SAFETY: the caller should guarantee that raw is indead of type `tpe`
    pub(super) unsafe fn from_raw(raw: OpaqueSlotData, tpe: expr::Type) -> Self {
        Self { raw, tpe }
    }
}

impl std::ops::Drop for SlotData {
    fn drop(&mut self) {
        // SAFETY: api designs of slot guarantee that data is always valid
        unsafe {
            match self.tpe {
                expr::Type::BV(width) => {
                    if width > 64 {
                        panic!("trying to drop a slot of size >64")
                    }
                }
                expr::Type::Array(ArrayType {
                    index_width,
                    data_width,
                }) => {
                    let (index_width, data_width) = (index_width as u64, data_width as u64);
                    if data_width > 64 {
                        panic!("trying to drop an array of width >64")
                    }

                    runtime::__dealloc_array(self.raw.0 as _, index_width, data_width);
                }
            }
        }
    }
}

/// contains an immutable reference to some opaque data and its type.
pub struct SlotEntry<'slot> {
    pub(super) slot: &'slot mut OpaqueSlotData,
    pub(super) tpe: expr::Type,
}

impl SlotEntry<'_> {
    pub fn insert(&mut self, mut data: SlotData) -> SlotData {
        assert_eq!(self.tpe, data.tpe);
        std::mem::swap(self.slot, &mut data.raw);
        data
    }

    /// SAFETY: the caller should guarantee that if the slot data is modified,
    /// it should still contain data of `tpe`
    pub unsafe fn raw_data_mut(&mut self) -> &mut u64 {
        &mut self.slot.0
    }
}
