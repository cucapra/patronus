use patronus::expr::{self};

use cranelift::codegen::ir;
use cranelift::prelude::*;

// code generation helpers that don't need to depend on other parts of CodeGenContext
pub(crate) fn try_swap_compiled_code_ret_with_slot(
    mut dst_slot: Value,
    src: Value,
    data_type: expr::Type,
    fn_build: &mut FunctionBuilder,
) {
    let w = data_type.get_bit_vector_width().unwrap();
    if !matches!(super::bv_codegen::select_container_primitive(w), types::I64) {
        dst_slot = fn_build.ins().uextend(types::I64, dst_slot);
    }
    fn_build
        .ins()
        .store(ir::MemFlags::trusted(), dst_slot, src, 0);
}
