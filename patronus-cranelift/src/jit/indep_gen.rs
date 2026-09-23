use patronus::expr::{self, WidthInt};

use cranelift::codegen::ir;
use cranelift::prelude::*;

// code generation helpers that don't need to depend on other parts of CodeGenContext
pub(crate) fn try_swap_compiled_code_ret_with_slot(
    dst_slot: Value,
    src: Value,
    data_type: expr::Type,
    fn_build: &mut FunctionBuilder,
) {
    if let expr::Type::BV(width) = data_type
        && width <= super::THIN_BV_MAX_WIDTH
    {
        store_thin_bv_at_slot(dst_slot, src, width, fn_build);
        return;
    }
    // `src` is interpreted as slot address of long lived heap resources
    swap_ptr_at_slot(fn_build, dst_slot, src);
}

pub(crate) fn swap_ptr_at_slot(fn_build: &mut FunctionBuilder, slot_a: Value, slot_b: Value) {
    let ptr_a = fn_build
        .ins()
        .load(super::INT_T, MemFlags::trusted(), slot_a, 0);
    let ptr_b = fn_build
        .ins()
        .load(super::INT_T, MemFlags::trusted(), slot_b, 0);
    fn_build.ins().store(MemFlags::trusted(), ptr_b, slot_a, 0);
    fn_build.ins().store(MemFlags::trusted(), ptr_a, slot_b, 0);
}

fn store_thin_bv_at_slot(
    slot: Value,
    mut ret: Value,
    width: WidthInt,
    fn_build: &mut FunctionBuilder,
) {
    if !matches!(
        super::bv_codegen::select_container_primitive(width),
        types::I64
    ) {
        ret = fn_build.ins().uextend(types::I64, ret);
    }
    fn_build.ins().store(ir::MemFlags::trusted(), ret, slot, 0);
}
