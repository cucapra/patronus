// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use super::runtime;
use patronus::expr::{self, *};
use patronus::system::*;
use rustc_hash::FxHashMap;

#[repr(transparent)]
pub(super) struct OpaqueSlotData(u64);

pub(super) struct SlotData {
    raw: OpaqueSlotData,
    tpe: expr::Type,
}

impl SlotData {
    pub(super) fn as_ref(&self) -> SlotDataRef<'_> {
        SlotDataRef::from_opaque_data(&self.raw, self.tpe)
    }
}

pub(super) trait SlotDataRefReduce {
    type Output;
    fn with_bit_vec(&mut self, data: &[u64], width: WidthInt) -> Self::Output;
    fn with_primitive_array<T: Into<u64> + Copy>(
        &mut self,
        data: &[T],
        index_width: WidthInt,
        data_width: WidthInt,
    ) -> Self::Output;
}

pub(super) trait SlotDataRefMutReduce {
    type Output;
    fn with_bit_vec(&mut self, data: &mut [u64], width: WidthInt) -> Self::Output;
    fn with_primitive_array<T: TryFrom<u64>>(
        &mut self,
        data: &mut [T],
        index_width: WidthInt,
        data_width: WidthInt,
    ) -> Self::Output;
}

#[derive(PartialEq, Eq)]
pub(super) struct SlotDataRef<'a> {
    pub kind: SlotDataRefKind<'a>,
    pub tpe: expr::Type,
}

pub(super) struct SlotDataRefMut<'a> {
    pub kind: SlotDataRefMutKind<'a>,
    pub tpe: expr::Type,
}

#[derive(PartialEq, Eq)]
pub(super) enum SlotDataRefKind<'a> {
    BitVec(&'a [u64]),
    ArrayU8(&'a [u8]),
    ArrayU16(&'a [u16]),
    ArrayU32(&'a [u32]),
    ArrayU64(&'a [u64]),
}

pub(super) enum SlotDataRefMutKind<'a> {
    BitVec(&'a mut [u64]),
    ArrayU8(&'a mut [u8]),
    ArrayU16(&'a mut [u16]),
    ArrayU32(&'a mut [u32]),
    ArrayU64(&'a mut [u64]),
}

/// The `StateBuffer` associates each `state` expression with an expr slot.
/// Its expr ledge routes each state's expr to slot offset.
pub(super) struct StateBuffer<'expr> {
    pub ledge: ExprLedge,
    pub ctx: &'expr Context,
    pub sys: &'expr TransitionSystem,
}

impl StateBuffer<'_> {
    // SAFETY: caller should guarantee that each slot in `self` and `other` contains the same data type
    pub unsafe fn swap(&mut self, other: &mut Self) {
        debug_assert!(
            self.ledge
                .dtypes
                .iter()
                .zip(&other.ledge.dtypes)
                .all(|(a, b)| a.eq(b))
        );
        std::mem::swap(&mut self.ledge.slots, &mut other.ledge.slots);
    }
}

pub(super) fn build_in_out_state_buffer<'a>(
    ctx: &'a Context,
    sys: &'a TransitionSystem,
) -> (StateBuffer<'a>, StateBuffer<'a>) {
    (StateBuffer::new(ctx, sys), StateBuffer::new(ctx, sys))
}

impl<'expr> StateBuffer<'expr> {
    fn new(ctx: &'expr Context, sys: &'expr TransitionSystem) -> Self {
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
        Self {
            ledge: ExprLedge::new(ctx, &exprs, move |e| offset_map.get(&e).copied()),
            ctx,
            sys,
        }
    }

    pub(super) fn get_state_offset(&self, symbol: ExprRef) -> usize {
        self.ledge
            .offset_query(symbol)
            .expect("queried symbol is not part of the state")
    }
}

impl Clone for StateBuffer<'_> {
    fn clone(&self) -> Self {
        let mut cloned_buffer = StateBuffer::new(self.ctx, self.sys);
        for (mut dst, src) in (&mut cloned_buffer.ledge).into_iter().zip(&self.ledge) {
            dst.copy_from(src);
        }
        cloned_buffer
    }
}

impl OpaqueSlotData {
    fn new(tpe: expr::Type) -> Self {
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

    fn as_bit_vec<'a>(&'a self, width: WidthInt) -> SlotDataRefKind<'a> {
        let words_slice = if width <= 64 {
            std::slice::from_ref(&self.0)
        } else {
            unsafe { runtime::bv_words_slice_from_raw_parts(self.0 as _, width as _) }
        };
        SlotDataRefKind::BitVec(words_slice)
    }

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

    fn as_bit_vec_mut<'a>(&'a mut self, width: WidthInt) -> SlotDataRefMutKind<'a> {
        let words_slice = if width <= 64 {
            std::slice::from_mut(&mut self.0)
        } else {
            unsafe { runtime::bv_words_slice_from_raw_parts_mut(self.0 as _, width as _) }
        };
        SlotDataRefMutKind::BitVec(words_slice)
    }

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

impl SlotData {
    /// SAFETY: the caller should guarantee that raw is indead of type `tpe`
    unsafe fn from_raw(raw: OpaqueSlotData, tpe: expr::Type) -> Self {
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
                        runtime::__dealloc_bv(self.raw.0 as _, width as u64)
                    }
                }
                expr::Type::Array(ArrayType {
                    index_width,
                    data_width,
                }) => {
                    let (index_width, data_width) = (index_width as u64, data_width as u64);
                    if data_width <= 64 {
                        runtime::__dealloc_array(self.raw.0 as _, index_width, data_width);
                    } else {
                        runtime::__dealloc_array_of_wide_bv(
                            self.raw.0 as _,
                            index_width,
                            data_width,
                        );
                    }
                }
            }
        }
    }
}

fn reinterp_array_ptr_with_element<'a, T>(data: &OpaqueSlotData, tpe: ArrayType) -> &'a [T] {
    unsafe { std::slice::from_raw_parts(data.0 as *const T, 1 << tpe.index_width) }
}

fn reinterp_array_ptr_with_element_mut<'a, T>(
    data: &mut OpaqueSlotData,
    tpe: ArrayType,
) -> &'a mut [T] {
    unsafe { std::slice::from_raw_parts_mut(data.0 as *mut T, 1 << tpe.index_width) }
}

impl<'a> SlotDataRef<'a> {
    fn from_opaque_data<'slot>(data: &'slot OpaqueSlotData, tpe: expr::Type) -> SlotDataRef<'slot> {
        let kind = match tpe {
            expr::Type::BV(width) => data.as_bit_vec(width),
            expr::Type::Array(array_tpe) => data.as_array(array_tpe),
        };
        SlotDataRef { kind, tpe }
    }

    pub(super) fn reduce<T>(&self, mut reducer: impl SlotDataRefReduce<Output = T>) -> T {
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
    fn from_opaque_data<'slot>(
        data: &'slot mut OpaqueSlotData,
        tpe: expr::Type,
    ) -> SlotDataRefMut<'slot> {
        let kind = match tpe {
            expr::Type::BV(width) => data.as_bit_vec_mut(width),
            expr::Type::Array(array_tpe) => data.as_array_mut(array_tpe),
        };
        SlotDataRefMut { kind, tpe }
    }

    pub(super) fn reduce<T>(&mut self, mut reducer: impl SlotDataRefMutReduce<Output = T>) -> T {
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

    pub(super) fn expect_bit_vec(self) -> &'a mut [u64] {
        if let SlotDataRefMutKind::BitVec(words) = self.kind {
            words
        } else {
            panic!("expect bit vec type")
        }
    }

    fn copy_from(&mut self, other: SlotDataRef<'_>) {
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

pub(super) struct SlotEntry<'slot> {
    slot: &'slot mut OpaqueSlotData,
    tpe: expr::Type,
}

impl SlotEntry<'_> {
    pub(super) fn insert(&mut self, mut data: SlotData) -> SlotData {
        assert_eq!(self.tpe, data.tpe);
        std::mem::swap(self.slot, &mut data.raw);
        data
    }

    /// SAFETY: the caller should guarantee that if the slot data is modified,
    /// it should still contain data of `tpe`
    pub(super) unsafe fn raw_data_mut(&mut self) -> &mut u64 {
        &mut self.slot.0
    }
}

pub(super) struct ExprLedge {
    pub slots: Box<[OpaqueSlotData]>,
    pub dtypes: Box<[expr::Type]>,
    pub offset_map: Box<dyn Fn(ExprRef) -> Option<usize>>,
}

impl ExprLedge {
    pub(super) fn new_singleton(ctx: &Context, expr: ExprRef) -> Self {
        Self::new(ctx, &[expr], |_| Some(0))
    }
    pub(super) fn new(
        ctx: &Context,
        exprs: &[ExprRef],
        offset_map: impl Fn(ExprRef) -> Option<usize> + 'static,
    ) -> Self {
        let mut assignment = FxHashMap::default();
        let dtypes: Vec<_> = exprs.iter().map(|&e| e.get_type(ctx)).collect();
        for (&e, dtype) in exprs.iter().zip(&dtypes) {
            assert!(
                assignment
                    .insert(
                        offset_map(e).expect("input expr not found"),
                        OpaqueSlotData::new(*dtype)
                    )
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
        Self {
            slots: slots.into_boxed_slice(),
            dtypes: dtypes.into_boxed_slice(),
            offset_map: Box::new(offset_map),
        }
    }

    pub(super) fn into_slot_data(mut self) -> Vec<SlotData> {
        self.steal_slot_data().collect()
    }

    fn steal_slot_data(&mut self) -> impl Iterator<Item = SlotData> {
        std::mem::take(&mut self.slots)
            .into_iter()
            .zip(std::mem::take(&mut self.dtypes))
            .map(|(raw, tpe)| unsafe { SlotData::from_raw(raw, tpe) })
    }

    pub(super) fn get_slot_data<'slot>(&'slot self, expr: ExprRef) -> Option<SlotDataRef<'slot>> {
        let offset = self.offset_query(expr)?;
        Some(self.get_slot_data_at_offset(offset))
    }

    pub(super) fn get_slot_data_mut<'slot>(
        &'slot mut self,
        expr: ExprRef,
    ) -> Option<SlotDataRefMut<'slot>> {
        let offset = self.offset_query(expr)?;
        Some(self.get_slot_data_at_offset_mut(offset))
    }

    #[inline]
    pub(super) fn get_slot_data_at_offset<'slot>(&'slot self, offset: usize) -> SlotDataRef<'slot> {
        SlotDataRef::from_opaque_data(&self.slots[offset], self.dtypes[offset])
    }

    #[inline]
    pub(super) fn get_slot_data_at_offset_mut<'slot>(
        &'slot mut self,
        offset: usize,
    ) -> SlotDataRefMut<'slot> {
        SlotDataRefMut::from_opaque_data(&mut self.slots[offset], self.dtypes[offset])
    }

    pub(super) fn offset_query(&self, expr: ExprRef) -> Option<usize> {
        (self.offset_map)(expr).filter(|&offset| offset < self.slots.len())
    }

    pub(super) fn entry(&mut self, expr: ExprRef) -> Option<SlotEntry<'_>> {
        let offset = self.offset_query(expr)?;
        Some(self.entry_at_offset(offset))
    }

    #[inline]
    pub(super) fn entry_at_offset(&mut self, offset: usize) -> SlotEntry<'_> {
        SlotEntry {
            slot: &mut self.slots[offset],
            tpe: self.dtypes[offset],
        }
    }

    /// SAFETY: the caller should guarantee that the invariant of expr ledge will not violated,
    /// i.e., they need to make sure each slot still contains pointer of correct type.
    pub(super) unsafe fn as_mut_raw_data_slice(&mut self) -> &mut [u64] {
        // SAFETY: `OpaqueSlotData` is transparent
        unsafe { std::mem::transmute::<&mut [OpaqueSlotData], &mut [u64]>(&mut *self.slots) }
    }

    pub(super) fn as_raw_data_slice(&self) -> &[u64] {
        // SAFETY: `OpaqueSlotData` is transparent
        unsafe { std::mem::transmute::<&[OpaqueSlotData], &[u64]>(&*self.slots) }
    }
}

impl std::ops::Drop for ExprLedge {
    fn drop(&mut self) {
        Vec::from_iter(self.steal_slot_data());
    }
}

pub(super) struct SlotIterRefMut<'slot> {
    ledge: &'slot mut ExprLedge,
    next: usize,
}

impl<'slot> Iterator for SlotIterRefMut<'slot> {
    type Item = SlotDataRefMut<'slot>;
    fn next(&mut self) -> Option<Self::Item> {
        let raw_ptr = self.ledge.slots.get_mut(self.next)? as *mut OpaqueSlotData;
        let tpe = self.ledge.dtypes.get(self.next).copied()?;
        self.next += 1;
        // SAFETY: iter emits mut borrow over each individual element
        unsafe { Some(SlotDataRefMut::from_opaque_data(&mut *raw_ptr, tpe)) }
    }
}

impl<'slot> IntoIterator for &'slot mut ExprLedge {
    type IntoIter = SlotIterRefMut<'slot>;
    type Item = SlotDataRefMut<'slot>;
    fn into_iter(self) -> Self::IntoIter {
        SlotIterRefMut {
            ledge: self,
            next: 0,
        }
    }
}

pub(super) struct SlotIterRef<'slot> {
    ledge: &'slot ExprLedge,
    next: usize,
}

impl<'slot> Iterator for SlotIterRef<'slot> {
    type Item = SlotDataRef<'slot>;
    fn next(&mut self) -> Option<Self::Item> {
        let raw = self.ledge.slots.get(self.next)?;
        let tpe = self.ledge.dtypes.get(self.next).copied()?;
        self.next += 1;
        Some(SlotDataRef::from_opaque_data(raw, tpe))
    }
}

impl<'slot> IntoIterator for &'slot ExprLedge {
    type IntoIter = SlotIterRef<'slot>;
    type Item = SlotDataRef<'slot>;
    fn into_iter(self) -> Self::IntoIter {
        SlotIterRef {
            ledge: self,
            next: 0,
        }
    }
}
