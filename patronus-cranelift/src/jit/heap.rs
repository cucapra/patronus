use std::marker::PhantomData;

use baa::Word;

pub(super) struct SlicedHeapResourceCache<T> {
    buffer: Pinnable<i64>,
    lens: Vec<usize>,
    phantom: PhantomData<T>,
}

impl<T> Default for SlicedHeapResourceCache<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> SlicedHeapResourceCache<T> {
    pub(super) fn new() -> Self {
        Self {
            buffer: Pinnable::default(),
            lens: Vec::default(),
            phantom: PhantomData,
        }
    }

    pub(super) fn pinned_start_address(&self) -> *const i64 {
        self.buffer.as_pinned_ptr()
    }

    pub(super) fn push(&mut self, item: Box<[T]>) {
        self.lens.push(item.len());
        self.buffer.push(Box::into_raw(item) as *mut T as i64);
    }

    pub(super) fn seal(&mut self) {
        self.buffer.pin();
    }
}

impl<T> std::ops::Drop for SlicedHeapResourceCache<T> {
    fn drop(&mut self) {
        for (&ptr, &len) in self.buffer.iter().zip(&self.lens) {
            unsafe {
                let _ = Box::from_raw(std::ptr::slice_from_raw_parts_mut(ptr as *mut T, len));
            }
        }
    }
}

/// A vector that can be potentially pinned on heap by `into_boxed_slice`.
/// The starting address of a pinned vector can no longer be changed through heap grow.
pub enum Pinnable<T> {
    Growable(Vec<T>),
    Pinned(Box<[T]>),
}

impl<T> Default for Pinnable<T> {
    fn default() -> Self {
        Self::Growable(Vec::default())
    }
}

impl<T> Pinnable<T> {
    fn iter(&self) -> impl Iterator<Item = &T> {
        match self {
            Pinnable::Growable(vec) => vec.iter(),
            Pinnable::Pinned(boxed) => boxed.iter(),
        }
    }

    fn push(&mut self, item: T) {
        match self {
            Self::Growable(v) => v.push(item),
            _ => panic!("pinned vector can not be updated"),
        }
    }

    fn pin(&mut self) {
        match self {
            Self::Growable(v) => *self = Self::Pinned(std::mem::take(v).into_boxed_slice()),
            _ => panic!("try call `pin` more than once"),
        }
    }

    fn as_pinned_ptr(&self) -> *const T {
        match self {
            Self::Pinned(boxed) => boxed.as_ptr(),
            _ => panic!("`pin` has never been called"),
        }
    }
}

#[derive(Default)]
pub(super) struct ManagedHeapResource {
    pub(super) bv_data: SlicedHeapResourceCache<Word>,
    pub(super) array_data: SlicedHeapResourceCache<u8>,
    /// TODO: resources reclaim this length erased pointer
    array_with_wide_bv_data: SlicedHeapResourceCache<*mut Word>,
}

impl ManagedHeapResource {
    pub(crate) fn seal(&mut self) {
        self.bv_data.seal();
        self.array_data.seal();
        self.array_with_wide_bv_data.seal();
    }
}
