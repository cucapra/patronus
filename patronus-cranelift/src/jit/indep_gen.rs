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
