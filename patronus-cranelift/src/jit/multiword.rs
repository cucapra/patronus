// utility implementation for multiword bitvectors

/*
TODO:
- basic, extremely naive, "set of words" implementation
- byte-granularity / finer width control
- more intelligent representations (perhaps lazy)
- clever codegen tricks
- caching zeroed constants
*/

use baa::{BitVecOps, BitVecValueRef};
use patronus::expr::WidthInt;
use smallvec::*;

use super::bv_codegen::select_contain_t;
use cranelift::codegen::ir::MemFlagsData;
use cranelift::prelude::*;

// change this if the size of a word ever changes
pub const WORD_WIDTH: usize = 64;
pub const WORD_T: Type = types::I64;

pub fn width_words(width: u32) -> usize {
    width.div_ceil(WORD_WIDTH as u32) as usize
}

#[derive(Clone)]
pub struct Bundle {
    pub words: SmallVec<[Value; 4]>,
    // higher index = later word
}

// handle codegen for a vector of a particular width

// apply some closure to the last partial word in the width, if it exists
fn apply_to_pword<F>(
    b: &mut FunctionBuilder,
    words: &mut SmallVec<[Value; 4]>,
    self_width: WidthInt,
    f: F,
) where
    F: Fn(&mut FunctionBuilder, Value, WidthInt) -> Value,
{
    let lpos = width_words(self_width);
    let rem_width = self_width % 64;
    if rem_width > 0 {
        words.get_mut(lpos).map(|e| *e = f(b, *e, rem_width));
    }
}

// TODO: rethink the padding semantics, it's almost certainly wrong somewhere

// pad a most significant word
// TODO: replace with normal sign extension
fn pad_msw(b: &mut FunctionBuilder, pad_t: bool, pad_bits: WidthInt, v: Value) -> Value {
    let lsh_r = b.ins().ishl_imm_u(v, pad_bits as i64);
    if pad_t {
        // pad ones
        b.ins().sshr_imm_u(lsh_r, pad_bits as i64)
    } else {
        // pad zeroes
        b.ins().ishl_imm_u(lsh_r, pad_bits as i64)
    }
}

impl Bundle {
    // require previous type
    // if previous type is narrower than WORD_WIDTH, extend
    pub fn from_scalar(
        b: &mut FunctionBuilder,
        prev_width: WidthInt,
        prev_v: Value,
        dest_width: WidthInt,
    ) -> Bundle {
        let prev_t = select_contain_t(prev_width);
        let fst_word = if prev_t.eq(&WORD_T) {
            prev_v
        } else {
            b.ins().uextend(WORD_T, prev_v)
        };

        let mut res = Self::zeroed(b, dest_width);
        res.words[0] = fst_word;

        res
    }

    // new zeroed
    pub fn zeroed(b: &mut FunctionBuilder, dest_width: WidthInt) -> Bundle {
        // TODO: possibly optimisable with SmallVec::from_const?
        let dest_words = width_words(dest_width);
        let zero_word = b.ins().iconst(WORD_T, 0);
        let pad_words = std::iter::repeat(zero_word).take(dest_words);
        let words = SmallVec::from_iter(pad_words);

        Bundle { words }
    }

    // literal
    pub fn from_lit(b: &mut FunctionBuilder, value: BitVecValueRef, width: WidthInt) -> Bundle {
        let mut res = Self::zeroed(b, width);

        for (i, wd) in value.words().iter().enumerate() {
            res.words[i] = b.ins().iconst(WORD_T, *wd as i64);
        }
        res
    }

    // load, store
    // NOTE: assumes that the load location contains width_words(width) of information, i.e. there is no additional zero-padding necessary.
    pub fn load_from(b: &mut FunctionBuilder, source: Value, width: WidthInt) -> Bundle {
        let dest_words = width_words(width);
        let words = SmallVec::from_iter((0..dest_words).map(|oset| {
            let offset = (oset * (WORD_WIDTH / 8)) as i32;
            b.ins()
                .load(WORD_T, MemFlagsData::trusted(), source, offset)
        }));
        Bundle { words }
    }

    pub fn store_to(&self, b: &mut FunctionBuilder, dest: Value, width: WidthInt) {
        assert_eq!(width_words(width), self.words.len());
        for (oset, word) in self.words.iter().enumerate() {
            let offset = (oset * (WORD_WIDTH / 8)) as i32;
            b.ins().store(MemFlagsData::trusted(), *word, dest, offset);
        }
    }

    // codegen methods

    // TODO: like above, but for 'full' words

    // pad (choose padding type: ones or zeroes)
    pub fn pad(
        &self,
        b: &mut FunctionBuilder,
        pad_t: bool,
        src_width: WidthInt,
        dest_width: WidthInt,
    ) -> Bundle {
        let mut new_w = self.words.clone();

        apply_to_pword(b, &mut new_w, src_width, |b, old_v, pad_amt| {
            pad_msw(b, pad_t, pad_amt, old_v)
        }); // need to pad remainder of the largest word
        let pad_to_go = dest_width - (src_width.next_multiple_of(64));

        // generate new words: subtract from dest_width, trying tot ake off either 64 or less
        let pad_full = pad_to_go / 64;
        if pad_full > 0 {
            let blanked_word = if pad_t {
                b.ins().iconst(WORD_T, i64::MAX)
            } else {
                b.ins().iconst(WORD_T, 0)
            };
            new_w.extend(std::iter::repeat(blanked_word).take(pad_full as usize))
        }
        // TODO: this will behave incorrectly: sign extension bits will not be carried upwards
        // first pad by pad_amt, then shift back to word boundary
        apply_to_pword(b, &mut new_w, dest_width, |b, old_v, pad_amt| {
            pad_msw(b, pad_t, pad_amt, old_v)
        });

        Bundle { words: new_w }
    }

    // mask any amount of bits starting at zero
    // for this, actually perform AND
    pub fn mask(
        &self,
        b: &mut FunctionBuilder,
        in_width: WidthInt,
        mask_width: WidthInt,
    ) -> Bundle {
        let mut new_w = self.words.clone();

        // perform masking on the last partial word in the mask
        apply_to_pword(b, &mut new_w, mask_width, |b, old_v, mask_amt| {
            b.ins().band_imm_u(old_v, (1 << mask_amt) - 1)
        });

        // then, mask the rest of the word
        let z_c = b.ins().iconst(types::I64, 0);
        // we can possibly save a few logical ops here by just resetting everything above to 0
        for rem_i in (in_width.next_multiple_of(64) as usize)..width_words(mask_width) {
            new_w[rem_i] = b.ins().band(new_w[rem_i], z_c);
        }

        Bundle { words: new_w }
    }

    // concat
    // self = 'hi', other = 'lo'
    pub fn concat(
        &self,
        b: &mut FunctionBuilder,
        other: &Bundle,
        hiwidth: WidthInt,
        lowidth: WidthInt,
    ) -> Bundle {
        todo!()

        // if lowidth is on word boundary, can just join the two vectors

        // otherwise:
        // requires that every word is zeroed above its given length
        // for every word in the hi:
        // - mask off the bits which would otherwise be shifted into another word
        // - put them (AND will work if result is zeroed) into the upper bits of the previous word
        // - right shift the current word
        // repeat until out of words
    }

    // TODO: concat of two word-level into one bundle

    // slice
    // determine word span
    // do the rotation trick
    pub fn slice(
        &self,
        b: &mut FunctionBuilder,
        in_width: WidthInt,
        lo: WidthInt,
        hi: WidthInt,
    ) -> Bundle {
        // https://github.com/cucapra/baa/blob/main/src/bv/arithmetic.rs#L117
        // determine the words which the slice region spans
        // complete words just get copied over wholesale
        // the incomplete words are masked appropriately
        todo!()
    }

    // slices which fit within a scalar constant
    pub fn slice_narrow(
        &self,
        b: &mut FunctionBuilder,
        in_width: WidthInt,
        lo: WidthInt,
        hi: WidthInt,
    ) -> Value {
        todo!()
    }

    // TODO: these could pass additional data to the closures, for now we will be lazy
    // map_op
    // useful for and, or, xor
    pub fn map_op<F>(
        &self,
        b: &mut FunctionBuilder,
        in_width: WidthInt,
        other: &Bundle,
        f: F,
    ) -> Bundle
    where
        F: Fn(&mut FunctionBuilder, Value, Value) -> Value,
    {
        let wc = width_words(in_width);
        let new_words = SmallVec::from_iter((0..wc).map(|i| {
            let l = self.words[i];
            let r = other.words[i];
            f(b, l, r)
        }));
        Bundle { words: new_words }
    }

    pub fn reduce<F>(&self, b: &mut FunctionBuilder, in_width: WidthInt, f: F) -> Value
    where
        F: Fn(&mut FunctionBuilder, Value, Value) -> Value,
    {
        let wc = width_words(in_width);
        let mut res = self.words[0];
        for i in 1..wc {
            let curr = self.words[i];
            res = f(b, res, curr);
        }
        res
    }
}
