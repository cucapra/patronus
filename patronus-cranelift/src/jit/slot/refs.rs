use super::base::*;
use super::converter::*;
use patronus::expr::{self, *};

#[derive(PartialEq, Eq)]
pub struct SlotDataRef<'a> {
    pub kind: SlotDataRefKind<'a>,
    pub tpe: expr::Type,
}

pub struct SlotDataRefMut<'a> {
    pub kind: SlotDataRefMutKind<'a>,
    pub tpe: expr::Type,
}

#[derive(PartialEq, Eq)]
pub enum SlotDataRefKind<'a> {
    BitVec(&'a [u64]),
    ArrayU8(&'a [u8]),
    ArrayU16(&'a [u16]),
    ArrayU32(&'a [u32]),
    ArrayU64(&'a [u64]),
}

pub enum SlotDataRefMutKind<'a> {
    BitVec(&'a mut [u64]),
    ArrayU8(&'a mut [u8]),
    ArrayU16(&'a mut [u16]),
    ArrayU32(&'a mut [u32]),
    ArrayU64(&'a mut [u64]),
}

/// given an OpaqueSlotData, reinterpret it as a pointer to an array with size specified by ``tpe``
fn reinterp_array_ptr_with_element<'a, T>(data: &OpaqueSlotData, tpe: ArrayType) -> &'a [T] {
    unsafe { std::slice::from_raw_parts(data.0 as *const T, 1 << tpe.index_width) }
}

/// given a OpaqueSlotData, reinterpret it as a mutable pointer to an array with size specified by ``tpe``
fn reinterp_array_ptr_with_element_mut<'a, T>(
    data: &mut OpaqueSlotData,
    tpe: ArrayType,
) -> &'a mut [T] {
    unsafe { std::slice::from_raw_parts_mut(data.0 as *mut T, 1 << tpe.index_width) }
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

    /// reinterpret as an array: points to owned memory
    fn as_array<'a>(&self, tpe: ArrayType) -> SlotDataRefKind<'a> {
        match tpe.data_width {
            1..=8 => SlotDataRefKind::ArrayU8(reinterp_array_ptr_with_element::<u8>(self, tpe)),
            9..=16 => SlotDataRefKind::ArrayU16(reinterp_array_ptr_with_element::<u16>(self, tpe)),
            17..=32 => SlotDataRefKind::ArrayU32(reinterp_array_ptr_with_element::<u32>(self, tpe)),
            33..=64 => SlotDataRefKind::ArrayU64(reinterp_array_ptr_with_element::<u64>(self, tpe)),
            65.. => panic!("array with elements >64b"),
            _ => panic!("zero sized array"),
        }
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

    /// reinterpret as an array: points to owned memory
    fn as_array_mut<'a>(&'a mut self, tpe: ArrayType) -> SlotDataRefMutKind<'a> {
        match tpe.data_width {
            1..=8 => {
                SlotDataRefMutKind::ArrayU8(reinterp_array_ptr_with_element_mut::<u8>(self, tpe))
            }
            9..=16 => {
                SlotDataRefMutKind::ArrayU16(reinterp_array_ptr_with_element_mut::<u16>(self, tpe))
            }
            17..=32 => {
                SlotDataRefMutKind::ArrayU32(reinterp_array_ptr_with_element_mut::<u32>(self, tpe))
            }
            33..=64 => {
                SlotDataRefMutKind::ArrayU64(reinterp_array_ptr_with_element_mut::<u64>(self, tpe))
            }
            65.. => panic!("array with elements >64b"),
            _ => panic!("zero sized array"),
        }
    }
}

impl<'a> SlotDataRef<'a> {
    pub(super) fn from_opaque_data<'slot>(
        data: &'slot OpaqueSlotData,
        tpe: expr::Type,
    ) -> SlotDataRef<'slot> {
        let kind = match tpe {
            expr::Type::BV(width) => data.as_bit_vec(width),
            expr::Type::Array(array_tpe) => data.as_array(array_tpe),
        };
        SlotDataRef { kind, tpe }
    }

    /// get a owned clone of the data at the referenced location
    pub fn reduce<T>(&self, mut reducer: impl SlotDataRefReduce<Output = T>) -> T {
        match self.kind {
            SlotDataRefKind::BitVec(data) => {
                reducer.with_bit_vec(data, self.tpe.get_bit_vector_width().unwrap())
            }
            _ => self.reduce_array_dispatch(reducer),
        }
    }

    fn reduce_array_dispatch<T>(&self, mut reducer: impl SlotDataRefReduce<Output = T>) -> T {
        let expr::Type::Array(ArrayType {
            index_width,
            data_width,
        }) = self.tpe
        else {
            unreachable!()
        };
        match &self.kind {
            SlotDataRefKind::ArrayU8(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            SlotDataRefKind::ArrayU16(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            SlotDataRefKind::ArrayU32(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            SlotDataRefKind::ArrayU64(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            _ => unreachable!(),
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
            expr::Type::Array(array_tpe) => data.as_array_mut(array_tpe),
        };
        SlotDataRefMut { kind, tpe }
    }

    pub fn reduce<T>(&mut self, mut reducer: impl SlotDataRefMutReduce<Output = T>) -> T {
        match &mut self.kind {
            SlotDataRefMutKind::BitVec(data) => {
                reducer.with_bit_vec(data, self.tpe.get_bit_vector_width().unwrap())
            }
            _ => self.reduce_array_dispatch(reducer),
        }
    }

    fn reduce_array_dispatch<T>(
        &mut self,
        mut reducer: impl SlotDataRefMutReduce<Output = T>,
    ) -> T {
        let expr::Type::Array(ArrayType {
            index_width,
            data_width,
        }) = self.tpe
        else {
            unreachable!()
        };
        match &mut self.kind {
            SlotDataRefMutKind::ArrayU8(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            SlotDataRefMutKind::ArrayU16(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            SlotDataRefMutKind::ArrayU32(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            SlotDataRefMutKind::ArrayU64(data) => {
                reducer.with_primitive_array(data, index_width, data_width)
            }
            _ => unreachable!(),
        }
    }

    pub fn expect_bit_vec(self) -> &'a mut [u64] {
        if let SlotDataRefMutKind::BitVec(words) = self.kind {
            words
        } else {
            panic!("expect bit vec type")
        }
    }

    pub(super) fn copy_from(&mut self, other: SlotDataRef<'_>) {
        assert_eq!(self.tpe, other.tpe);
        match (&mut self.kind, other.kind) {
            (SlotDataRefMutKind::BitVec(dst), SlotDataRefKind::BitVec(src)) => {
                dst.copy_from_slice(src)
            }
            (SlotDataRefMutKind::ArrayU8(dst), SlotDataRefKind::ArrayU8(src)) => {
                dst.copy_from_slice(src)
            }
            (SlotDataRefMutKind::ArrayU16(dst), SlotDataRefKind::ArrayU16(src)) => {
                dst.copy_from_slice(src)
            }
            (SlotDataRefMutKind::ArrayU32(dst), SlotDataRefKind::ArrayU32(src)) => {
                dst.copy_from_slice(src)
            }
            (SlotDataRefMutKind::ArrayU64(dst), SlotDataRefKind::ArrayU64(src)) => {
                dst.copy_from_slice(src)
            }
            _ => unreachable!(),
        }
    }
}
