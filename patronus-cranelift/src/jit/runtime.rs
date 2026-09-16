// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use baa::Word;
use cranelift::codegen::ir::{AbiParam, FuncRef, Function, types};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;

pub(super) struct RuntimeLib {
    pub(super) dealloc_array: FuncRef,
    pub(super) alloc_array: FuncRef,

    pub(super) copy_from_array: FuncRef,

    pub(super) copy_from_bv: FuncRef,
}

const CLONE_ARRAY_SYM: &str = "__clone_array";
const CLONE_ARRAY_OF_WIDE_BV_SYM: &str = "__clone_array_of_wide_bv";
const DEALLOC_ARRAY_SYM: &str = "__dealloc_array";
const DEALLOC_ARRAY_OF_WIDE_BV_SYM: &str = "__dealloc_array_of_wide_bv";
const ALLOC_ARRAY_SYM: &str = "__alloc_array";
const ALLOC_ARRAY_OF_WIDE_BV_SYM: &str = "__alloc_array_of_wide_bv";
const COPY_FROM_ARRAY_SYM: &str = "__copy_from_array";
const COPY_FROM_ARRAY_OF_WIDE_BV_SYM: &str = "__copy_from_array_of_wide_bv";
const CLONE_BV_SYM: &str = "__clone_bv";
const DEALLOC_BV_SYM: &str = "__dealloc_bv";
const COPY_FROM_BV_SYM: &str = "__copy_from_bv";

pub(super) fn load_runtime_lib(builder: &mut JITBuilder) {
    builder.symbol(CLONE_ARRAY_SYM, __clone_array as *const u8);
    builder.symbol(
        CLONE_ARRAY_OF_WIDE_BV_SYM,
        __clone_array_of_wide_bv as *const u8,
    );
    builder.symbol(DEALLOC_ARRAY_SYM, __dealloc_array as *const u8);
    builder.symbol(
        DEALLOC_ARRAY_OF_WIDE_BV_SYM,
        __dealloc_array_of_wide_bv as *const u8,
    );
    builder.symbol(ALLOC_ARRAY_SYM, __alloc_array as *const u8);
    builder.symbol(
        ALLOC_ARRAY_OF_WIDE_BV_SYM,
        __alloc_array_of_wide_bv as *const u8,
    );
    builder.symbol(COPY_FROM_ARRAY_SYM, __copy_from_array as *const u8);
    builder.symbol(
        COPY_FROM_ARRAY_OF_WIDE_BV_SYM,
        __copy_from_array_of_wide_bv as *const u8,
    );
    builder.symbol(CLONE_BV_SYM, __clone_bv as *const u8);
    builder.symbol(DEALLOC_BV_SYM, __dealloc_bv as *const u8);
    builder.symbol(COPY_FROM_BV_SYM, __copy_from_bv as *const u8);
}

pub(super) fn import_runtime_lib_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> RuntimeLib {
    let dealloc_array =
        import_extern_function(module, func, DEALLOC_ARRAY_SYM, [types::I64; 3], []);
    let alloc_array =
        import_extern_function(module, func, ALLOC_ARRAY_SYM, [types::I64; 3], [types::I64]);

    let copy_from_array =
        import_extern_function(module, func, COPY_FROM_ARRAY_SYM, [types::I64; 4], []);

    let copy_from_bv = import_extern_function(module, func, COPY_FROM_BV_SYM, [types::I64; 3], []);

    RuntimeLib {
        dealloc_array,

        alloc_array,

        copy_from_array,
        copy_from_bv,
    }
}

fn import_extern_function(
    module: &mut JITModule,
    func: &mut Function,
    name: &str,
    params: impl IntoIterator<Item = types::Type>,
    returns: impl IntoIterator<Item = types::Type>,
) -> FuncRef {
    let mut sig = module.make_signature();
    sig.params = Vec::from_iter(params.into_iter().map(AbiParam::new));
    sig.returns = Vec::from_iter(returns.into_iter().map(AbiParam::new));
    sig.call_conv = isa::CallConv::SystemV;

    let id = module
        .declare_function(name, Linkage::Import, &sig)
        .unwrap_or_else(|reason| panic!("fail to load {name}, due to {reason:#?}"));
    module.declare_func_in_func(id, func)
}

macro_rules! reinterp_array_ptr_by_data_width {
    ($ptr: ident, $data_width: expr, $op: tt) => {
        $crate::jit::runtime::reinterp_array_ptr_by_data_width!(
            [$ptr], $data_width, $op
        )
    };

    ([$($ptr: ident),+], $data_width: expr, $op: tt) => {
        $crate::jit::runtime::reinterp_array_ptr_by_data_width!(
            @dispatch [($($ptr),+)], $data_width,
            [1..=8 => i8, 9..=16 => i16, 17..=32 => i32, 33..=64 => i64],
            $op
        )
    };

    (@dispatch [$ptr: tt], $data_width: expr, [$($pat: pat => $primitive:ty),+], $op: tt) => {
        match $data_width {
           $(
                $pat => {
                    $crate::jit::runtime::reinterp_array_ptr_by_data_width!(@cast [$ptr], $primitive, $op)
                },
           )+
           _ => unreachable!()
        }
    };

    (@cast [($($ptr: ident),+)], $primitive: ty, $op: tt) => {
        #[allow(unused_braces)]
        {
            $(let $ptr = $ptr as *mut $primitive;)+
            $op
        }
    }
}
pub(super) use reinterp_array_ptr_by_data_width;

pub(super) unsafe extern "C" fn __clone_array(
    src: *const (),
    index_width: u64,
    data_width: u64,
) -> *mut () {
    reinterp_array_ptr_by_data_width!(src, data_width, {
        let len = 1 << index_width;
        let mut array = vec![0; len];
        let src = unsafe { std::slice::from_raw_parts(src, len) };
        array.copy_from_slice(src);
        array.leak() as *mut [_] as *mut ()
    })
}

pub(super) unsafe extern "C" fn __clone_array_of_wide_bv(
    src: *const *const Word,
    index_width: u64,
    data_width: u64,
) -> *const *mut Word {
    unsafe {
        let len = 1 << index_width;
        let mut array = Vec::with_capacity(len);
        let src = std::slice::from_raw_parts(src, len);
        array.extend(src.iter().map(|&bv| __clone_bv(bv, data_width)));
        array.leak() as *const [*mut Word] as *const *mut Word
    }
}

pub(super) unsafe extern "C" fn __copy_from_array(
    dst: *mut (),
    src: *const (),
    index_width: u64,
    data_width: u64,
) {
    let len = 1 << index_width;
    reinterp_array_ptr_by_data_width!([dst, src], data_width, {
        unsafe {
            let dst = std::slice::from_raw_parts_mut(dst, len);
            let src = std::slice::from_raw_parts_mut(src, len);
            dst.copy_from_slice(src)
        }
    })
}

pub(super) unsafe extern "C" fn __copy_from_array_of_wide_bv(
    dst: *const *mut Word,
    src: *const *const Word,
    index_width: u64,
    data_width: u64,
) {
    unsafe {
        let len = 1 << index_width;
        let dst = std::slice::from_raw_parts(dst, len);
        let src = std::slice::from_raw_parts(src, len);
        dst.iter()
            .zip(src.iter())
            .for_each(|(&dst_bv, &src_bv)| __copy_from_bv(dst_bv, src_bv, data_width));
    }
}

macro_rules! alloc_array_of_data_width {
    ($default: expr, $index_width: expr, $data_width: expr, [$($pat: pat => $primitive: ty),+]) => {
        match $data_width{
            $(
                $pat=> vec![$default as $primitive; 1 << $index_width].leak() as *mut [$primitive] as *mut (),
            )+
            _ => unreachable!()
        }
    }
}

pub(super) extern "C" fn __alloc_array(
    default_data: i64,
    index_width: u64,
    data_width: u64,
) -> *mut () {
    alloc_array_of_data_width!(
        default_data, index_width, data_width,
        [1..=8 => i8, 9..=16 => i16, 17..=32 => i32, 33..=64 => i64]
    )
}

pub(super) unsafe extern "C" fn __alloc_array_of_wide_bv(
    default_data: *const Word,
    index_width: u64,
    data_width: u64,
) -> *const *mut Word {
    let len = 1 << index_width;
    unsafe {
        Vec::from_iter(std::iter::repeat_with(|| __clone_bv(default_data, data_width)).take(len))
            .leak() as *const [*mut Word] as *const *mut Word
    }
}

pub(super) unsafe extern "C" fn __dealloc_array(src: *mut (), index_width: u64, data_width: u64) {
    reinterp_array_ptr_by_data_width!(src, data_width, {
        let len = 1 << index_width;
        let ptr = std::ptr::slice_from_raw_parts_mut(src, len);
        unsafe {
            let _ = Box::from_raw(ptr);
        }
    })
}

pub(super) unsafe extern "C" fn __dealloc_array_of_wide_bv(
    src: *mut *mut Word,
    index_width: u64,
    data_width: u64,
) {
    unsafe {
        let len = 1 << index_width;
        let array = std::slice::from_raw_parts_mut(src, len);
        for &bv in array.iter() {
            __dealloc_bv(bv, data_width);
        }
        let _ = Box::from_raw(array);
    }
}

pub(super) extern "C" fn __alloc_bv(width: u64) -> *mut Word {
    Box::leak(reserve_bv_boxed_words(width)) as *mut [Word] as *mut Word
}

pub(super) unsafe extern "C" fn __clone_bv(src: *const Word, width: u64) -> *mut Word {
    let dst = __alloc_bv(width);
    unsafe {
        bv_words_slice_from_raw_parts_mut(dst, width)
            .copy_from_slice(bv_words_slice_from_raw_parts(src, width));
    }
    dst
}

pub(super) unsafe extern "C" fn __dealloc_bv(src: *mut Word, width: u64) {
    unsafe {
        let _ = Box::from_raw(bv_words_slice_from_raw_parts_mut(src, width));
    }
}

pub(super) unsafe extern "C" fn __copy_from_bv(dst: *mut Word, src: *const Word, width: u64) {
    unsafe {
        bv_words_slice_from_raw_parts_mut(dst, width)
            .copy_from_slice(bv_words_slice_from_raw_parts(src, width));
    }
}

#[inline]
pub(super) fn reserve_bv_boxed_words(width: u64) -> Box<[Word]> {
    vec![0; width.div_ceil(Word::BITS as u64) as usize].into_boxed_slice()
}

/// Construct the underlying words buffer given starting address and bit vector's width
///
/// # Safety
/// The caller should guarantee that `ptr` points to a valid word buffer reserved for bit vector of `width`
#[inline]
pub(super) unsafe fn bv_words_slice_from_raw_parts<'a>(ptr: *const Word, width: u64) -> &'a [Word] {
    unsafe { std::slice::from_raw_parts(ptr, width.div_ceil(Word::BITS as u64) as usize) }
}

/// Construct the underlying words buffer given starting address and bit vector's width
///
/// # Safety
/// The caller should guarantee that `ptr` points to a valid word buffer reserved for bit vector of `width`
#[inline]
pub(super) unsafe fn bv_words_slice_from_raw_parts_mut<'a>(
    ptr: *mut Word,
    width: u64,
) -> &'a mut [Word] {
    unsafe { std::slice::from_raw_parts_mut(ptr, width.div_ceil(Word::BITS as u64) as usize) }
}
// pub(super) use {bv_value_mut, bv_value_ref, bv_value_ref_from_scalar};
