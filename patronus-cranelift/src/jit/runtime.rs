// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use baa::Word;
use cranelift::codegen::ir::{AbiParam, FuncRef, Function, types};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;
use patronus::expr::*;
use rustc_hash::FxHashMap;
use trampoline::*;

pub(super) struct RuntimeLib {
    pub(super) dealloc_array: FuncRef,
    pub(super) dealloc_array_of_wide_bv: FuncRef,
    pub(super) alloc_array: FuncRef,
    pub(super) alloc_array_of_wide_bv: FuncRef,
    pub(super) copy_from_array: FuncRef,
    pub(super) copy_from_array_of_wide_bv: FuncRef,
    pub(super) dealloc_bv: FuncRef,
    pub(super) copy_from_bv: FuncRef,
    pub(super) bv_ops: FxHashMap<&'static str, FuncRef>,
}
inventory::collect!(trampoline::BVOpRegistry);

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
    for registered in inventory::iter::<trampoline::BVOpRegistry>() {
        builder.symbol(
            bv_operation_name_mangle(registered.sym),
            registered.raw_address(),
        );
    }
}

pub(super) fn import_runtime_lib_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> RuntimeLib {
    let dealloc_array =
        import_extern_function(module, func, DEALLOC_ARRAY_SYM, [types::I64; 3], []);
    let dealloc_array_of_wide_bv = import_extern_function(
        module,
        func,
        DEALLOC_ARRAY_OF_WIDE_BV_SYM,
        [types::I64; 3],
        [],
    );
    let alloc_array =
        import_extern_function(module, func, ALLOC_ARRAY_SYM, [types::I64; 3], [types::I64]);
    let alloc_array_of_wide_bv = import_extern_function(
        module,
        func,
        ALLOC_ARRAY_OF_WIDE_BV_SYM,
        [types::I64; 3],
        [types::I64],
    );
    let copy_from_array =
        import_extern_function(module, func, COPY_FROM_ARRAY_SYM, [types::I64; 4], []);
    let copy_from_array_of_wide_bv = import_extern_function(
        module,
        func,
        COPY_FROM_ARRAY_OF_WIDE_BV_SYM,
        [types::I64; 4],
        [],
    );

    let dealloc_bv = import_extern_function(module, func, DEALLOC_BV_SYM, [types::I64; 2], []);
    let copy_from_bv = import_extern_function(module, func, COPY_FROM_BV_SYM, [types::I64; 3], []);

    RuntimeLib {
        dealloc_array,
        dealloc_array_of_wide_bv,
        alloc_array,
        alloc_array_of_wide_bv,
        copy_from_array,
        copy_from_array_of_wide_bv,
        dealloc_bv,
        copy_from_bv,
        bv_ops: import_bv_runtime_to_func_scope(module, func),
    }
}

fn import_bv_runtime_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> FxHashMap<&'static str, FuncRef> {
    let mut bv_runtime_lib = FxHashMap::default();
    for registered in inventory::iter::<BVOpRegistry>() {
        let num_params = match registered.kind {
            BVOpKind::Unary(_) | BVOpKind::Cmp(_) => 3,
            BVOpKind::Binary(_) | BVOpKind::Slice(_) | BVOpKind::Extend(_) => 4,
            BVOpKind::SliceWithOutputBuffer(_) | BVOpKind::Shift(_) | BVOpKind::Concat(_) => 5,
        };
        let return_types: &[types::Type] = match registered.kind {
            BVOpKind::Cmp(_) => &[types::I8],
            BVOpKind::Slice(_) => &[types::I64],
            _ => &[],
        };
        let func_ref = import_extern_function(
            module,
            func,
            &bv_operation_name_mangle(registered.sym),
            std::iter::repeat_n(types::I64, num_params),
            return_types.iter().copied(),
        );
        bv_runtime_lib.insert(registered.sym, func_ref);
    }
    bv_runtime_lib
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

#[inline]
fn bv_operation_name_mangle(sym: &str) -> String {
    format!("__bv_{sym}")
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

macro_rules! bv_value_ref {
    ($ptr: expr, $width: expr) => {
        baa::BitVecValueRef::new(
            $crate::jit::runtime::bv_words_slice_from_raw_parts($ptr, $width as u64),
            $width as baa::WidthInt,
        )
    };
}

macro_rules! bv_value_ref_from_scalar {
    ($value: expr, $width: expr) => {
        baa::BitVecValueRef::new(std::slice::from_ref(&$value), $width as baa::WidthInt)
    };
}

macro_rules! bv_value_mut {
    ($ptr: expr, $width: expr) => {
        baa::BitVecValueMutRef::new(
            $width as baa::WidthInt,
            $crate::jit::runtime::bv_words_slice_from_raw_parts_mut($ptr, $width as u64),
        )
    };
}
// pub(super) use {bv_value_mut, bv_value_ref, bv_value_ref_from_scalar};

mod trampoline {
    use super::*;
    use baa::{BitVecMutOps, BitVecOps};

    pub(super) struct BVOpRegistry {
        pub(super) sym: &'static str,
        pub(super) kind: BVOpKind,
    }

    impl BVOpRegistry {
        pub(super) fn raw_address(&self) -> *const u8 {
            match self.kind {
                BVOpKind::Binary(address) => address as *const u8,
                BVOpKind::Unary(address) => address as *const u8,
                BVOpKind::Cmp(address) => address as *const u8,
                BVOpKind::Slice(address) => address as *const u8,
                BVOpKind::SliceWithOutputBuffer(address) => address as *const u8,
                BVOpKind::Concat(address) => address as *const u8,
                BVOpKind::Extend(address) => address as *const u8,
                BVOpKind::Shift(address) => address as *const u8,
            }
        }
    }
    type MaybeIndirect = u64;
    type ThinBV = i64;
    pub(super) enum BVOpKind {
        Binary(unsafe extern "C" fn(*mut Word, *const Word, *const Word, u64)),
        Unary(unsafe extern "C" fn(*mut Word, *const Word, u64)),
        Cmp(unsafe extern "C" fn(*const Word, *const Word, u64) -> i8),
        Slice(unsafe extern "C" fn(*const Word, u64, u64, u64) -> ThinBV),
        SliceWithOutputBuffer(unsafe extern "C" fn(*mut Word, *const Word, u64, u64, u64)),
        Concat(unsafe extern "C" fn(*mut Word, MaybeIndirect, MaybeIndirect, u64, u64)),
        Extend(unsafe extern "C" fn(*mut Word, MaybeIndirect, u64, u64)),
        Shift(unsafe extern "C" fn(*mut Word, *const Word, u64, MaybeIndirect, u64)),
    }

    macro_rules! baa_binary_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_binary_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };
        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Binary($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut Word,
                lhs: *const Word,
                rhs: *const Word,
                width: u64,
            ) {
                unsafe {
                    bv_value_mut!(dst, width)
                        .$baa_delegation(&bv_value_ref!(lhs, width), &bv_value_ref!(rhs, width))
                }
            }
        }
    }

    macro_rules! baa_cmp_op_shim {
        ($($op: ident $([rename: $rename: ident])?),*) => {
            $(
                baa_cmp_op_shim!(@maybe_rename $op $(,$rename)?);
            )*
        };

        (@maybe_rename $op: ident, $rename: ident) => {
            paste::paste! {
                baa_cmp_op_shim!(@internal [<__bv_ $op>], $op, $rename);
            }
        };

        (@maybe_rename $op: ident) => {
            paste::paste! {
                baa_cmp_op_shim!(@internal [<__bv_ $op>], $op, $op);
            }
        };

        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Cmp($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(lhs: *const Word, rhs: *const Word, width: u64) -> i8 {
                unsafe { bv_value_ref!(lhs, width).$baa_delegation(&bv_value_ref!(rhs, width)) as i8 }
            }
        };
    }

    macro_rules! baa_unary_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_unary_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };
        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Unary($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(dst: *mut Word, value: *const Word, width: u64) {
                unsafe {
                    bv_words_slice_from_raw_parts_mut(dst, width)
                        .copy_from_slice(bv_words_slice_from_raw_parts(value, width));
                    bv_value_mut!(dst, width).$baa_delegation();
                }
            }
        };
    }

    macro_rules! baa_extend_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_extend_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };
        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Extend($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut Word,
                value: MaybeIndirect,
                original_width: u64,
                by: u64,
            ) { unsafe {
                let value = if original_width <= 64 {
                    &bv_value_ref_from_scalar!(value, original_width)
                } else {
                    &bv_value_ref!(value as *const Word, original_width)
                };
                bv_value_mut!(dst, original_width + by).$baa_delegation(value, by as WidthInt);
            }}
        };
    }
    macro_rules! baa_shift_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_shift_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };

        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Shift($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut Word,
                value: *const Word,
                width: u64,
                shift: MaybeIndirect,
                shift_data_width: u64,
            ) {
                unsafe {
                    let shift = if shift_data_width <= 64 {
                        bv_value_ref_from_scalar!(shift, shift_data_width)
                    } else {
                        bv_value_ref!(shift as *const Word, shift_data_width)
                    };
                    bv_value_mut!(dst, width).$baa_delegation(&bv_value_ref!(value, width), &shift);
                }
            }
        };
    }
    baa_binary_op_shim!(add, sub, mul, and, or, xor);
    baa_shift_op_shim!(shift_right, arithmetic_shift_right, shift_left);
    baa_extend_op_shim!(sign_extend, zero_extend);
    baa_unary_op_shim!(not, negate);
    baa_cmp_op_shim!(
        is_greater [rename: gt],
        is_greater_or_equal [rename: ge],
        is_greater_signed [rename: gt_signed],
        is_greater_or_equal_signed [rename: ge_signed],
        is_equal [rename: equal]
    );

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::Slice(__bv_slice),
        sym: "slice"
    });
    pub(super) unsafe extern "C" fn __bv_slice(
        value: *const Word,
        value_width: u64,
        hi: u64,
        lo: u64,
    ) -> ThinBV {
        unsafe {
            bv_value_ref!(value, value_width)
                .slice(hi as WidthInt, lo as WidthInt)
                .to_u64()
                .unwrap() as ThinBV
        }
    }

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::SliceWithOutputBuffer(__bv_slice_with_output_buffer),
        sym: "slice_with_output_buffer"
    });
    pub(super) unsafe extern "C" fn __bv_slice_with_output_buffer(
        dst: *mut Word,
        value: *const Word,
        value_width: u64,
        hi: u64,
        lo: u64,
    ) {
        unsafe {
            debug_assert!((hi - lo + 1) > 64);
            bv_value_mut!(dst, hi - lo + 1).slice_in_place(
                &bv_value_ref!(value, value_width),
                hi as WidthInt,
                lo as WidthInt,
            )
        }
    }

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::Concat(__bv_concat),
        sym: "concat"
    });
    pub(super) unsafe extern "C" fn __bv_concat(
        dst: *mut Word,
        hi: MaybeIndirect,
        lo: MaybeIndirect,
        hi_width: u64,
        lo_width: u64,
    ) {
        unsafe {
            let hi = if hi_width <= 64 {
                bv_value_ref_from_scalar!(hi, hi_width)
            } else {
                bv_value_ref!(hi as *const Word, hi_width)
            };
            let lo = if lo_width <= 64 {
                bv_value_ref_from_scalar!(lo, lo_width)
            } else {
                bv_value_ref!(lo as *const Word, lo_width)
            };
            bv_value_mut!(dst, hi_width + lo_width).concat_in_place(&hi, &lo);
        }
    }
}
