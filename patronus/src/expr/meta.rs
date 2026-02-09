// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Expression Metadata
//! Provides the `[ExprMetaData]` trait and a dense as well as sparse implementation for it.

use super::ExprRef;
use baa::Word;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Debug;
use std::ops::{Index, IndexMut};

pub trait ExprMap<T>:
    Debug + Clone + Index<ExprRef, Output = T> + IndexMut<ExprRef, Output = T>
where
    T: Default + Clone + PartialEq,
{
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a;

    fn non_default_value_keys(&self) -> impl Iterator<Item = ExprRef>;
}

/// finds the fixed point value and updates values it discovers along the way
pub fn get_fixed_point<T: ExprMap<Option<ExprRef>>>(m: &mut T, key: ExprRef) -> Option<ExprRef> {
    // fast path without updating any pointers
    if key == m[key]? {
        return Some(key);
    }

    // pointer chasing, similar to union find, but not the asymptotically fast path halving version
    let mut value = key;
    while value != m[value]? {
        value = m[value]?;
    }
    // update pointers
    let final_value = value;
    value = key;
    while value != final_value {
        let next = m[value]?;
        m[value] = Some(final_value);
        value = next;
    }
    Some(value)
}

/// A sparse hash map to stare meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct SparseExprMap<T: Default + Clone + Debug> {
    inner: FxHashMap<ExprRef, T>,
    // we need actual storage so that we can return a reference
    default: T,
}

impl<T: Default + Clone + Debug> Index<ExprRef> for SparseExprMap<T> {
    type Output = T;

    #[inline]
    fn index(&self, e: ExprRef) -> &Self::Output {
        self.inner.get(&e).unwrap_or(&self.default)
    }
}

impl<T: Default + Clone + Debug> IndexMut<ExprRef> for SparseExprMap<T> {
    #[inline]
    fn index_mut(&mut self, e: ExprRef) -> &mut Self::Output {
        self.inner.entry(e).or_default()
    }
}

impl<T: Default + Clone + Debug + PartialEq> ExprMap<T> for SparseExprMap<T> {
    #[inline]
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a,
    {
        self.inner.iter().map(|(k, v)| (*k, v))
    }

    #[inline]
    fn non_default_value_keys(&self) -> impl Iterator<Item = ExprRef> {
        self.inner
            .iter()
            .filter(|(_, v)| **v != T::default())
            .map(|(k, _)| *k)
    }
}

/// A dense hash map to store meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct DenseExprMetaData<T: Default + Clone + Debug> {
    inner: Vec<T>,
    // we need actual storage so that we can return a reference
    default: T,
}

impl<T: Default + Clone + Debug> DenseExprMetaData<T> {
    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }
}

impl<T: Default + Clone + Debug> Index<ExprRef> for DenseExprMetaData<T> {
    type Output = T;

    #[inline]
    fn index(&self, e: ExprRef) -> &Self::Output {
        self.inner.get(e.index()).unwrap_or(&self.default)
    }
}

impl<T: Default + Clone + Debug> IndexMut<ExprRef> for DenseExprMetaData<T> {
    #[inline]
    fn index_mut(&mut self, e: ExprRef) -> &mut Self::Output {
        if self.inner.len() <= e.index() {
            self.inner.resize(e.index() + 1, T::default());
        }
        &mut self.inner[e.index()]
    }
}

impl<T: Default + Clone + Debug + PartialEq> ExprMap<T> for DenseExprMetaData<T> {
    #[inline]
    fn iter<'a>(&'a self) -> impl Iterator<Item = (ExprRef, &'a T)>
    where
        T: 'a,
    {
        ExprMetaDataIter {
            inner: self.inner.iter(),
            index: 0,
        }
    }

    fn non_default_value_keys(&self) -> impl Iterator<Item = ExprRef> {
        self.iter()
            .filter(|(_, v)| **v != T::default())
            .map(|(k, _)| k)
    }
}

struct ExprMetaDataIter<'a, T> {
    inner: std::slice::Iter<'a, T>,
    index: usize,
}

impl<'a, T> Iterator for ExprMetaDataIter<'a, T> {
    type Item = (ExprRef, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(value) => {
                let index_ref = ExprRef::from_index(self.index);
                self.index += 1;
                Some((index_ref, value))
            }
        }
    }
}

pub trait ExprSet {
    fn contains(&self, value: &ExprRef) -> bool;
    fn insert(&mut self, value: ExprRef) -> bool;
    fn remove(&mut self, value: &ExprRef) -> bool;
}

/// A dense  map to store boolean meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct DenseExprSet {
    inner: Vec<u64>,
}

impl ExprSet for DenseExprSet {
    fn contains(&self, value: &ExprRef) -> bool {
        let (word_idx, bit) = index_to_word_and_bit(*value);
        let word = self.inner.get(word_idx).cloned().unwrap_or_default();
        ((word >> bit) & 1) == 1
    }

    fn insert(&mut self, value: ExprRef) -> bool {
        let (word_idx, bit) = index_to_word_and_bit(value);
        if self.inner.len() <= word_idx {
            self.inner.resize(word_idx + 1, 0);
        }
        let bit_was_set = ((self.inner[word_idx] >> bit) & 1) == 1;
        self.inner[word_idx] |= 1u64 << bit;
        !bit_was_set
    }

    fn remove(&mut self, value: &ExprRef) -> bool {
        let (word_idx, bit) = index_to_word_and_bit(*value);
        if self.inner.len() <= word_idx {
            false
        } else {
            let bit_was_set = ((self.inner[word_idx] >> bit) & 1) == 1;
            self.inner[word_idx] &= !(1u64 << bit);
            bit_was_set
        }
    }
}

#[inline]
fn index_to_word_and_bit(index: ExprRef) -> (usize, u32) {
    let index = index.index();
    let word = index / Word::BITS as usize;
    let bit = index % Word::BITS as usize;
    (word, bit as u32)
}

/// A dense hash map to store boolean meta-data related to each expression
#[derive(Debug, Default, Clone)]
pub struct SparseExprSet {
    inner: FxHashSet<ExprRef>,
}

impl ExprSet for SparseExprSet {
    fn contains(&self, value: &ExprRef) -> bool {
        self.inner.contains(value)
    }

    fn insert(&mut self, value: ExprRef) -> bool {
        self.inner.insert(value)
    }

    fn remove(&mut self, value: &ExprRef) -> bool {
        self.inner.remove(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_fixed_point() {
        let mut m = DenseExprMetaData::default();
        let zero = ExprRef::from_index(0);
        let one = ExprRef::from_index(1);
        let two = ExprRef::from_index(2);
        m[zero] = Some(one);
        m[one] = Some(two);
        m[two] = Some(two);

        assert_eq!(get_fixed_point(&mut m, two), Some(two));
        assert_eq!(get_fixed_point(&mut m, one), Some(two));
        assert_eq!(get_fixed_point(&mut m, zero), Some(two));
        // our current implementation updates the whole path
        assert_eq!(m[zero], Some(two));
        assert_eq!(m[one], Some(two));
    }

    #[test]
    fn test_dense_bool() {
        let mut m = DenseExprSet::default();
        assert!(!m.contains(&ExprRef::from_index(7)));
        m.insert(ExprRef::from_index(7));
        assert!(m.contains(&ExprRef::from_index(7)));
    }
}
