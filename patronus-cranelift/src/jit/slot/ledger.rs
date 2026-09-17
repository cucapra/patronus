use super::base::*;
use super::refs::*;
use patronus::expr::{self, *};
use rustc_hash::FxHashMap;

pub struct ExprLedge {
    pub slots: Box<[OpaqueSlotData]>,
    pub dtypes: Box<[expr::Type]>,
    pub offset_map: Box<dyn Fn(ExprRef) -> Option<usize>>,
}

impl ExprLedge {
    pub fn new_singleton(ctx: &Context, expr: ExprRef) -> Self {
        Self::new(ctx, &[expr], |_| Some(0))
    }
    pub fn new(
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

    pub fn into_slot_data(mut self) -> Vec<SlotData> {
        self.steal_slot_data().collect()
    }

    fn steal_slot_data(&mut self) -> impl Iterator<Item = SlotData> {
        std::mem::take(&mut self.slots)
            .into_iter()
            .zip(std::mem::take(&mut self.dtypes))
            .map(|(raw, tpe)| unsafe { SlotData::from_raw(raw, tpe) })
    }

    pub fn get_slot_data<'slot>(&'slot self, expr: ExprRef) -> Option<SlotDataRef<'slot>> {
        let offset = self.offset_query(expr)?;
        Some(self.get_slot_data_at_offset(offset))
    }

    pub fn get_slot_data_mut<'slot>(
        &'slot mut self,
        expr: ExprRef,
    ) -> Option<SlotDataRefMut<'slot>> {
        let offset = self.offset_query(expr)?;
        Some(self.get_slot_data_at_offset_mut(offset))
    }

    #[inline]
    pub fn get_slot_data_at_offset<'slot>(&'slot self, offset: usize) -> SlotDataRef<'slot> {
        SlotDataRef::from_opaque_data(&self.slots[offset], self.dtypes[offset])
    }

    #[inline]
    pub(super) fn get_slot_data_at_offset_mut<'slot>(
        &'slot mut self,
        offset: usize,
    ) -> SlotDataRefMut<'slot> {
        SlotDataRefMut::from_opaque_data(&mut self.slots[offset], self.dtypes[offset])
    }

    pub fn offset_query(&self, expr: ExprRef) -> Option<usize> {
        (self.offset_map)(expr).filter(|&offset| offset < self.slots.len())
    }

    pub fn entry(&mut self, expr: ExprRef) -> Option<SlotEntry<'_>> {
        let offset = self.offset_query(expr)?;
        Some(self.entry_at_offset(offset))
    }

    #[inline]
    pub fn entry_at_offset(&mut self, offset: usize) -> SlotEntry<'_> {
        SlotEntry {
            slot: &mut self.slots[offset],
            tpe: self.dtypes[offset],
        }
    }

    /// SAFETY: the caller should guarantee that the invariant of expr ledge will not violated,
    /// i.e., they need to make sure each slot still contains pointer of correct type.
    pub unsafe fn as_mut_raw_data_slice(&mut self) -> &mut [u64] {
        // SAFETY: `OpaqueSlotData` is transparent
        unsafe { std::mem::transmute::<&mut [OpaqueSlotData], &mut [u64]>(&mut *self.slots) }
    }

    pub fn as_raw_data_slice(&self) -> &[u64] {
        // SAFETY: `OpaqueSlotData` is transparent
        unsafe { std::mem::transmute::<&[OpaqueSlotData], &[u64]>(&*self.slots) }
    }
}

impl std::ops::Drop for ExprLedge {
    fn drop(&mut self) {
        Vec::from_iter(self.steal_slot_data());
    }
}

// boilerplate for iterating over an exprledge
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

/// iterator over the data stored in ExprLedge, returning mutable references that are correctly typed
pub struct SlotIterRefMut<'slot> {
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

/// iterator over the data stored in ExprLedge, returning references that are correctly typed
pub struct SlotIterRef<'slot> {
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
