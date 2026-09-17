// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use super::bv_codegen::{self, iconst, select_container_primitive};
use super::expr_graph::*;
use super::heap::*;
use super::slot::{ExprLedge, StateBuffer};
use super::{JITResult, THIN_BV_MAX_WIDTH, runtime};
use patronus::expr::{self, *};
use patronus::system::*;

use cranelift::codegen::ir;
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::Module;
use cranelift::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) struct JITCompiler {
    module: JITModule,
    pub(super) sealed_heap_resources: Vec<ManagedHeapResource>,
    pub(super) active_heap_resource: ManagedHeapResource,
}

pub(super) struct EvalBatchedExprWithUpdate(extern "C" fn(*const u64, *mut u64));

impl EvalBatchedExprWithUpdate {
    /// # Safety
    /// caller should guarantee the memory allocated for compiled code has not been reclaimed
    pub(super) unsafe fn call(&self, current_states: &[u64], next_states: &mut [u64]) {
        (self.0)(current_states.as_ptr(), next_states.as_mut_ptr())
    }
}

impl JITCompiler {
    pub(super) fn new(flags: Option<&str>) -> Self {
        let mut default_flags = FxHashMap::from_iter([("regalloc_algorithm", "single_pass")]);
        default_flags.extend(
            flags
                .map(|s| {
                    s.split(",").map(|flag| {
                        flag.split_once(":")
                            .expect("flag should be a `:` separated pair")
                    })
                })
                .into_iter()
                .flatten(),
        );
        let mut builder = JITBuilder::with_flags(
            &Vec::from_iter(default_flags),
            cranelift::module::default_libcall_names(),
        )
        .unwrap_or_else(|err| panic!("fail to launch jit instance, due to: {err:?}"));
        runtime::load_runtime_lib(&mut builder);

        Self {
            module: JITModule::new(builder),
            sealed_heap_resources: vec![],
            active_heap_resource: Default::default(),
        }
    }

    fn seal_active_heap_resource(&mut self) {
        self.active_heap_resource.seal();
        self.sealed_heap_resources
            .push(std::mem::take(&mut self.active_heap_resource));
    }

    fn last_pinned_heap_resource(&self) -> Option<&ManagedHeapResource> {
        self.sealed_heap_resources.last()
    }

    pub(super) fn compile_transition_sys(
        &mut self,
        expr_ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &StateBuffer<'_>,
        output_state_buffer: &StateBuffer<'_>,
    ) -> JITResult<EvalBatchedExprWithUpdate> {
        let (next_expr_batch, states_expr): (Vec<_>, Vec<_>) = sys
            .states
            .iter()
            .filter_map(|state| state.next.map(|next| (next, state.symbol)))
            .unzip();
        self.compile_batched_update_with_output_slots(
            expr_ctx,
            &next_expr_batch,
            input_state_buffer,
            &Vec::from_iter(
                states_expr
                    .into_iter()
                    .map(|sym| output_state_buffer.get_state_offset(sym)),
            ),
            true,
        )
    }

    pub(super) fn compile_batched_expr_eval(
        &mut self,
        expr_ctx: &expr::Context,
        expr_batch: &[ExprRef],
        input_state_buffer: &StateBuffer<'_>,
        output_ledge: &mut ExprLedge,
    ) -> JITResult<EvalBatchedExprWithUpdate> {
        let slot_offset = Vec::from_iter(
            expr_batch
                .iter()
                .map(|&sym| output_ledge.offset_query(sym).unwrap()),
        );
        self.compile_batched_update_with_output_slots(
            expr_ctx,
            expr_batch,
            input_state_buffer,
            &slot_offset,
            false,
        )
    }

    pub(super) fn compile_batched_update_with_output_slots(
        &mut self,
        expr_ctx: &expr::Context,
        expr_batch: &[ExprRef],
        input_state_buffer: &StateBuffer<'_>,
        slot_offset: &[usize],
        consume_input: bool,
    ) -> JITResult<EvalBatchedExprWithUpdate> {
        assert_eq!(expr_batch.len(), slot_offset.len());
        let sig = Signature {
            params: vec![AbiParam::new(types::I64), AbiParam::new(types::I64)],
            returns: vec![],
            call_conv: isa::CallConv::SystemV,
        };
        self.enter_compile_ctx_with(
            sig,
            expr_ctx,
            expr_batch,
            input_state_buffer,
            consume_input,
            |batch, mut codegen_ctx| {
                for ((&expr, &offset), ret) in
                    std::iter::zip(expr_batch.iter().zip(slot_offset), batch)
                {
                    let param_offset = offset as u32;
                    let output_buffer_address =
                        codegen_ctx.fn_builder.block_params(codegen_ctx.block_id)[1];
                    let data_type = expr.get_type(expr_ctx);
                    let dst_slot = codegen_ctx.fn_builder.ins().iadd_imm(
                        output_buffer_address,
                        (param_offset * codegen_ctx.int.bytes()) as i64,
                    );
                    try_swap_compiled_code_ret_with_slot(
                        dst_slot,
                        ret,
                        data_type,
                        &mut codegen_ctx,
                    );
                }
                codegen_ctx.fn_builder.ins().return_(&[]);
                codegen_ctx.fn_builder.finalize();
            },
        )
        .map(|address| unsafe {
            // SAFETY: upheld by the unsafeness of call method
            EvalBatchedExprWithUpdate(std::mem::transmute::<
                *const u8,
                extern "C" fn(*const u64, *mut u64),
            >(address))
        })
    }

    fn enter_compile_ctx_with<F>(
        &mut self,
        sig: Signature,
        expr_ctx: &expr::Context,
        expr_batch: &[ExprRef],
        input_state_buffer: &StateBuffer<'_>,
        consume_input: bool,
        codegen_epilogue: F,
    ) -> JITResult<*const u8>
    where
        F: FnOnce(Vec<Value>, CodeGenContext),
    {
        let mut cranelift_ctx = self.module.make_context();
        cranelift_ctx.func.signature = sig;

        let runtime_lib =
            runtime::import_runtime_lib_to_func_scope(&mut self.module, &mut cranelift_ctx.func);

        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut cranelift_ctx.func, &mut fn_builder_ctx);

        let entry_block = fn_builder.create_block();
        fn_builder.append_block_params_for_function_params(entry_block);
        fn_builder.switch_to_block(entry_block);
        fn_builder.seal_block(entry_block);

        let codegen_ctx = CodeGenContext {
            fn_builder,
            runtime_lib,
            block_id: entry_block,
            expr_ctx,
            expr_batch,
            input_state_buffer,
            short_lived_heap_allocation: FxHashSet::default(),
            compiler: self,
            int: types::I64,
            long_live_cache_read_holes: vec![],
            consume_input,
        };
        codegen_ctx.codegen(codegen_epilogue);

        let function_id = self
            .module
            .declare_anonymous_function(&cranelift_ctx.func.signature)?;
        self.module
            .define_function(function_id, &mut cranelift_ctx)?;
        self.module.clear_context(&mut cranelift_ctx);
        self.module.finalize_definitions()?;

        Ok(self.module.get_finalized_function(function_id))
    }
}

fn try_swap_compiled_code_ret_with_slot(
    dst_slot: Value,
    src: Value,
    data_type: expr::Type,
    codegen_ctx: &mut CodeGenContext,
) {
    if let expr::Type::BV(width) = data_type
        && width <= THIN_BV_MAX_WIDTH
    {
        store_thin_bv_at_slot(dst_slot, src, width, codegen_ctx);
        return;
    }
    // `src` is interpreted as slot address of long lived heap resources
    swap_ptr_at_slot(codegen_ctx, dst_slot, src);
}

fn store_thin_bv_at_slot(
    slot: Value,
    mut ret: Value,
    width: WidthInt,
    codegen_ctx: &mut CodeGenContext,
) {
    if !matches!(
        super::bv_codegen::select_container_primitive(width),
        types::I64
    ) {
        ret = codegen_ctx.fn_builder.ins().uextend(types::I64, ret);
    }
    codegen_ctx
        .fn_builder
        .ins()
        .store(ir::MemFlags::trusted(), ret, slot, 0);
}

fn swap_ptr_at_slot(codegen_ctx: &mut CodeGenContext, slot_a: Value, slot_b: Value) {
    let builder = &mut codegen_ctx.fn_builder;
    let ptr_a = builder
        .ins()
        .load(codegen_ctx.int, MemFlags::trusted(), slot_a, 0);
    let ptr_b = builder
        .ins()
        .load(codegen_ctx.int, MemFlags::trusted(), slot_b, 0);
    builder.ins().store(MemFlags::trusted(), ptr_b, slot_a, 0);
    builder.ins().store(MemFlags::trusted(), ptr_a, slot_b, 0);
}

pub(super) struct CodeGenContext<'expr, 'ctx, 'engine> {
    pub(super) fn_builder: FunctionBuilder<'ctx>,
    pub(super) runtime_lib: runtime::RuntimeLib,
    pub(super) expr_ctx: &'expr expr::Context,
    block_id: Block,
    expr_batch: &'engine [ExprRef],
    input_state_buffer: &'engine StateBuffer<'expr>,
    short_lived_heap_allocation: FxHashSet<TaggedValue>,
    pub(super) compiler: &'ctx mut JITCompiler,
    pub(super) int: cranelift::prelude::Type,
    /// Points to the dummy instruction that will be replaced with a read instruction from long lived heap resources buffer.
    /// These replacement operations are done after codegen, when the number of long lived cache are determined.
    long_live_cache_read_holes: Vec<(Value, expr::Type)>,
    consume_input: bool,
}

impl CodeGenContext<'_, '_, '_> {
    fn codegen<F: FnOnce(Vec<Value>, Self)>(mut self, epilogue: F) {
        let ret = self.mock_interpret();
        self.finalize_long_lived_heap_resources();
        epilogue(ret, self);
    }

    fn mock_interpret(&mut self) -> Vec<Value> {
        let mut evaluated: FxHashMap<ExprRef, TaggedValue> = FxHashMap::default();
        let bottom_up_expr_graph =
            BottomUpExprGraph::from_top_down_graph(self.expr_ctx, self.expr_batch);

        // Track direct depedents of each array related expr node.
        // This allows us to determine whether we could steal heap allocated resources from operand expression.
        let mut array_references: FxHashMap<ExprRef, FxHashSet<ExprRef>> = bottom_up_expr_graph
            .node_dependents
            .iter()
            .filter_map(|(&expr, dependents)| {
                if expr.get_type(self.expr_ctx).is_array() {
                    Some((expr, FxHashSet::from_iter(dependents.iter().copied())))
                } else {
                    None
                }
            })
            .collect();

        let mut arguments = Vec::with_capacity(4);
        // Postpone `ArrayStore` as much as possible to reduce unnecessary clone of potentially huge array
        let fringe_compare = |a: &ExprRef, _: &ExprRef| {
            if matches!(self.expr_ctx[*a], Expr::ArrayStore { .. }) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Less
            }
        };
        let walker = bottom_up_expr_graph.walker_with_sorted_fringe(&fringe_compare);
        for e in walker {
            let expr = &self.expr_ctx[e];
            expr.for_each_child(|child| {
                if child.get_type(self.expr_ctx).is_array() {
                    array_references.get_mut(child).unwrap().remove(&e);
                }
                arguments.push(evaluated[child]);
            });
            if let Expr::ArrayStore { array, .. } = expr {
                if array_references[array].iter().any(|&other| {
                    debug_assert!(!independent_expressions(&bottom_up_expr_graph, e, other));
                    !(matches!(self.expr_ctx[other], Expr::ArrayIte { .. })
                        && is_parent_of(&other, &bottom_up_expr_graph, e))
                }) {
                    let cow_slot = self.reserve_intermediate_array_cache_slot(
                        expr.get_array_type(self.expr_ctx).unwrap(),
                    );
                    let cow = self.resource_ptr_at_slot(cow_slot);
                    let src = self.resource_ptr_at_slot(evaluated[array]);
                    self.copy_from_array(cow, src);
                    // first argument of `ArrayStore` operation is the src array
                    arguments[0] = cow_slot;
                }
            }
            evaluated.insert(e, self.expr_codegen(e, &arguments));
            arguments.drain(..);
        }
        self.reclaim_short_lived_heap_resources();
        self.expr_batch.iter().map(|e| *evaluated[e]).collect()
    }

    /// Heap allocations registered with this function are considered to be short lived as opposed to long lived cache.
    /// They have lifetime that ties to the eval function. Therefore, they will introduce heap transactions per eval function call.
    fn register_short_lived_heap_allocation(&mut self, value: TaggedValue) {
        self.short_lived_heap_allocation.insert(value);
    }

    fn reclaim_short_lived_heap_resources(&mut self) {
        for value in self.short_lived_heap_allocation.clone() {
            match value.data_type {
                expr::Type::Array(..) => self.dealloc_array(value),
                _ => panic!("trying to deallocate wide bitvec"),
            }
        }
    }

    /// Register a hole that will be filled with pinned slot address of the resource after `mock_interpret` is done.
    ///
    /// We maintain the invariance that for every long lived heap resource there is a slot that contains the raw heap pointer
    /// to that during the entire lifetime of compiler. And that slot address won't change.
    fn phantom_register_long_lived_heap_resources(&mut self, tpe: expr::Type) -> TaggedValue {
        let phantom_src_addr = iconst!(self, 0);
        self.long_live_cache_read_holes
            .push((phantom_src_addr, tpe));
        TaggedValue::tag(phantom_src_addr, tpe)
    }

    /// Allocates all registered long-lived heap resources and pins them in a continuous buffer on heap.
    /// This extra level of indirection allows us to "swap" heap pointer with external pointer when necessary to reduce
    /// unnecessary heap allocation or data copy.
    fn finalize_long_lived_heap_resources(&mut self) {
        let mut array_holes: Vec<Value> = vec![];
        for &(value, tpe) in &self.long_live_cache_read_holes {
            match tpe {
                expr::Type::BV(width) => {
                    if width > 64 {
                        panic!("trying to finalise a bitvec >64b")
                    }
                }
                expr::Type::Array(ArrayType {
                    index_width,
                    data_width,
                }) => {
                    if data_width > THIN_BV_MAX_WIDTH {
                        panic!("trying to finalise an array of vecs >64b")
                    }
                    let ptr = runtime::__alloc_array(0, index_width as u64, data_width as u64);
                    let num_bytes = (1 << (index_width as usize))
                        * (select_container_primitive(data_width).bytes() as usize);
                    // SAFETY: `ptr` is always byte aligned and the coerced bytes slice len is computed properly
                    let boxed_bytes = unsafe {
                        Box::from_raw(std::ptr::slice_from_raw_parts_mut(
                            ptr as *mut u8,
                            num_bytes,
                        ))
                    };
                    self.compiler
                        .active_heap_resource
                        .array_data
                        .push(boxed_bytes);
                    array_holes.push(value);
                }
            }
        }
        self.compiler.seal_active_heap_resource();
        let last_pinned = self.compiler.last_pinned_heap_resource().unwrap();
        self.finalize_pinned_heap_resources(
            array_holes,
            last_pinned.array_data.pinned_start_address(),
        );
    }

    fn finalize_pinned_heap_resources(
        &mut self,
        dummy_inst_values: impl IntoIterator<Item = Value>,
        pinned_start_address: *const i64,
    ) {
        for (offset, value) in dummy_inst_values.into_iter().enumerate() {
            self.fill_heap_cache_read_hole(
                value,
                (pinned_start_address as usize) + offset * size_of::<i64>(),
            )
        }
    }

    /// Removes the dummy instruction hole and fills it with the actual slot address.
    /// Since the slot address is guaranteed to be pinned during the lifetime of compiler, it's sound for us to directly
    /// hardcode the raw address with `iconst` inst.
    fn fill_heap_cache_read_hole(&mut self, dummy_inst_value: Value, src_addr: usize) {
        let ir::dfg::ValueDef::Result(dummy_inst, _) =
            self.fn_builder.func.dfg.value_def(dummy_inst_value)
        else {
            unreachable!()
        };
        self.fn_builder
            .func
            .dfg
            .replace(dummy_inst)
            .iconst(self.int, src_addr as i64);
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct TaggedValue {
    pub(super) value: Value,
    pub(super) data_type: expr::Type,
}

impl std::ops::Deref for TaggedValue {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl TaggedValue {
    pub(super) fn requires_bv_delegation(&self) -> bool {
        if let expr::Type::BV(width) = self.data_type {
            if width > THIN_BV_MAX_WIDTH {
                panic!("bv delegation")
            }
        }
        false
    }

    pub(super) fn expect_array_type(&self) -> ArrayType {
        match self.data_type {
            expr::Type::Array(tpe) => tpe,
            _ => panic!("expect array type"),
        }
    }

    pub(super) fn expect_bv_type(&self) -> WidthInt {
        match self.data_type {
            expr::Type::BV(tpe) => tpe,
            _ => panic!("expect bitvec type"),
        }
    }

    pub(super) fn tag(value: Value, data_type: expr::Type) -> Self {
        Self { value, data_type }
    }

    pub(super) fn tag_bv(value: Value, width: WidthInt) -> Self {
        Self::tag(value, expr::Type::BV(width))
    }

    pub(super) fn tag_array(value: Value, tpe: ArrayType) -> Self {
        Self::tag(value, expr::Type::Array(tpe))
    }
}

impl CodeGenContext<'_, '_, '_> {
    /// the meaning of the input state is polymorphic over bv/array
    pub(super) fn load_input_state(&mut self, expr: ExprRef) -> TaggedValue {
        let slot_address = self.input_state_slot(expr);
        let value = self.fn_builder.ins().load(
            self.int,
            // buffer is allocated by Rust, therefore trusted
            ir::MemFlags::trusted(),
            *slot_address,
            0,
        );
        TaggedValue::tag(value, expr.get_type(self.expr_ctx))
    }

    fn input_state_slot(&mut self, expr: ExprRef) -> TaggedValue {
        let param_offset = self.input_state_buffer.get_state_offset(expr) as u32;
        let input_buffer_address = self.fn_builder.block_params(self.block_id)[0];
        let param_offset = iconst!(self, param_offset * self.int.bytes());
        let slot_address = self
            .fn_builder
            .ins()
            .iadd(input_buffer_address, param_offset);
        TaggedValue::tag(slot_address, expr.get_type(self.expr_ctx))
    }

    /// Reserves a long lived array cache, whose lifetime is tied to the JITCompiler
    /// It is not registered as per-step heap allocation, therefore can be used across multiple steps to reduce heap transaction
    fn reserve_intermediate_array_cache_slot(&mut self, tpe: ArrayType) -> TaggedValue {
        self.phantom_register_long_lived_heap_resources(expr::Type::Array(tpe))
    }

    /// Reserves a long lived wide bit vector cache, whose lifetime is tied to the JITCompiler
    /// It is not registered as per-step heap allocation, therefore can be used across multiple steps to reduce heap transaction
    pub(super) fn reserve_intermediate_bv_cache_slot(&mut self, width: WidthInt) -> TaggedValue {
        assert!(width > THIN_BV_MAX_WIDTH);
        self.phantom_register_long_lived_heap_resources(expr::Type::BV(width))
    }

    pub(super) fn resource_ptr_at_slot(&mut self, slot_address: TaggedValue) -> TaggedValue {
        let ret = self
            .fn_builder
            .ins()
            .load(types::I64, ir::MemFlags::trusted(), *slot_address, 0);
        TaggedValue::tag(ret, slot_address.data_type)
    }

    fn copy_from_array(&mut self, dst: TaggedValue, src: TaggedValue) {
        let ArrayType {
            index_width,
            data_width,
        } = dst.expect_array_type();
        assert_eq!(src.data_type, dst.data_type);
        if data_width > THIN_BV_MAX_WIDTH {
            panic!("attempting to copy an array of wide bv");
        }

        let callee = self.runtime_lib.copy_from_array;
        let (index_width, data_width) = (iconst!(self, index_width), iconst!(self, data_width));
        self.fn_builder
            .ins()
            .call(callee, &[*dst, *src, index_width, data_width]);
    }

    fn dealloc_array(&mut self, array_to_dealloc: TaggedValue) {
        let ArrayType {
            index_width,
            data_width,
        } = array_to_dealloc.expect_array_type();
        if data_width > THIN_BV_MAX_WIDTH {
            panic!("attempting to deallocate an array of wide bv");
        }
        let callee = self.runtime_lib.dealloc_array;
        let (index_width, data_width) = (iconst!(self, index_width), iconst!(self, data_width));
        self.fn_builder
            .ins()
            .call(callee, &[*array_to_dealloc, index_width, data_width]);
    }

    fn alloc_array(&mut self, default_data: TaggedValue, tpe: ArrayType) -> TaggedValue {
        if tpe.data_width > THIN_BV_MAX_WIDTH {
            panic!("attempting to allocate an array of wide bv");
        }

        let callee = self.runtime_lib.alloc_array;
        let (index_width, data_width) = (
            iconst!(self, tpe.index_width),
            iconst!(self, tpe.data_width),
        );
        let call = self
            .fn_builder
            .ins()
            .call(callee, &[*default_data, index_width, data_width]);
        let ret = TaggedValue::tag_array(self.fn_builder.inst_results(call)[0], tpe);
        self.register_short_lived_heap_allocation(ret);
        ret
    }

    pub(super) fn copy_from_bv(&mut self, dst: TaggedValue, src: TaggedValue) {
        assert_eq!(src.data_type, dst.data_type);
        let width = iconst!(self, dst.expect_bv_type());
        self.fn_builder
            .ins()
            .call(self.runtime_lib.copy_from_bv, &[*dst, *src, width]);
    }

    fn reserve_cloned_intermediate_cache_slot(&mut self, src: TaggedValue) -> TaggedValue {
        match src.data_type {
            expr::Type::Array(tpe) => {
                let slot = self.reserve_intermediate_array_cache_slot(tpe);
                let dst = self.resource_ptr_at_slot(slot);
                self.copy_from_array(dst, src);
                slot
            }
            expr::Type::BV(tpe) => {
                let slot = self.reserve_intermediate_bv_cache_slot(tpe);
                let dst = self.resource_ptr_at_slot(slot);
                self.copy_from_bv(dst, src);
                slot
            }
        }
    }

    /// Compute byte offset for bit vector element of `data_width` at `index`
    fn array_offset(&mut self, index: TaggedValue, data_width: WidthInt) -> Value {
        // TODO: support wide bv index type
        assert!(index.expect_bv_type() <= THIN_BV_MAX_WIDTH);
        let index = bv_codegen::BVWord(64).extend_to_fit(index, self);
        let item_size = if data_width <= THIN_BV_MAX_WIDTH {
            select_container_primitive(data_width).bytes()
        } else {
            types::I64.bytes()
        };
        self.fn_builder.ins().imul_imm(index, item_size as i64)
    }

    fn expr_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> TaggedValue {
        let value = match &self.expr_ctx[expr] {
            Expr::ArraySymbol { .. } => {
                // declared new arrays
                if !self.consume_input {
                    let input = self.load_input_state(expr);
                    return self.reserve_cloned_intermediate_cache_slot(input);
                } else {
                    let input_slot = self.input_state_slot(expr);
                    let cache_slot =
                        self.reserve_intermediate_array_cache_slot(input_slot.expect_array_type());
                    swap_ptr_at_slot(self, *cache_slot, *input_slot);
                    return cache_slot;
                }
            }
            Expr::BVIte { .. } | Expr::ArrayIte { .. } => {
                assert_eq!(args[1].data_type, args[2].data_type);
                self.fn_builder.ins().select(*args[0], *args[1], *args[2])
            }
            Expr::ArrayStore { .. } => {
                let ArrayType { data_width, .. } = args[0].expect_array_type();
                let (slot, index, data) = (args[0], args[1], args[2]);
                let base = self.resource_ptr_at_slot(slot);
                let offset = self.array_offset(index, data_width);
                let address = self.fn_builder.ins().iadd(*base, offset);
                if data_width > THIN_BV_MAX_WIDTH {
                    panic!("attempting to store to array of wide bv");
                }
                self.fn_builder.ins().store(
                    // upheld by the unsafeness of CompiledEvalFn::call
                    ir::MemFlags::trusted(),
                    *data,
                    address,
                    0,
                );

                return slot;
            }
            Expr::BVArrayRead { .. } => {
                let ArrayType { data_width, .. } = args[0].expect_array_type();
                let (slot, index) = (args[0], args[1]);
                let base = self.resource_ptr_at_slot(slot);
                let index = bv_codegen::BVWord(64).extend_to_fit(index, self);
                if data_width > THIN_BV_MAX_WIDTH {
                    panic!("attempting to read array of wide bv");
                }

                let element_type = types::I64;
                let offset = self
                    .fn_builder
                    .ins()
                    .imul_imm(index, element_type.bytes() as i64);
                let address = self.fn_builder.ins().iadd(*base, offset);
                let element = self.fn_builder.ins().load(
                    element_type,
                    // upheld by the unsafeness of CompiledEvalFn::call
                    ir::MemFlags::trusted(),
                    address,
                    0,
                );
                element
            }
            Expr::ArrayConstant { .. } => {
                let tpe = expr.get_array_type(self.expr_ctx).unwrap();
                // XXX: get rid of the extra alloc
                let default_value = if !args[0].requires_bv_delegation() {
                    self.fn_builder.ins().uextend(types::I64, *args[0])
                } else {
                    *args[0]
                };
                let array_const = self.alloc_array(
                    TaggedValue::tag_bv(default_value, args[0].expect_bv_type()),
                    tpe,
                );
                return self.reserve_cloned_intermediate_cache_slot(array_const);
            }
            _ => self.dispatch_bv_operation_codegen(expr, args),
        };
        TaggedValue::tag(value, expr.get_type(self.expr_ctx))
    }

    // dispatch an operation
    fn dispatch_bv_operation_codegen(&mut self, expr: ExprRef, args: &[TaggedValue]) -> Value {
        let width = expr.get_bv_type(self.expr_ctx).unwrap();
        if width > 64 {
            panic!("tried to generate code for a bitvec wider than 64b")
        }
        let vtable = bv_codegen::BVWord::new(width);
        let args: Vec<_> = args
            .iter()
            .map(|&arg| {
                if arg.requires_bv_delegation() {
                    self.resource_ptr_at_slot(arg)
                } else {
                    arg
                }
            })
            .collect();

        match self.expr_ctx[expr] {
            Expr::BVSymbol { .. } => vtable.symbol(expr, self),
            Expr::BVLiteral(value) => vtable.literal(value.get(self.expr_ctx), self),
            // unary
            Expr::BVNot(..) => vtable.not(args[0], self),
            Expr::BVNegate(..) => vtable.negate(args[0], self),
            // no-op with current impl
            Expr::BVZeroExt { by, .. } => vtable.zero_extend(args[0], by, self),
            Expr::BVSignExt { by, .. } => vtable.sign_extend(args[0], by, self),
            Expr::BVSlice { hi, lo, .. } => vtable.slice(args[0], hi, lo, self),
            // binary
            Expr::BVAdd(..) => vtable.add(args[0], args[1], self),
            Expr::BVSub(..) => vtable.sub(args[0], args[1], self),
            Expr::BVMul(..) => vtable.mul(args[0], args[1], self),
            Expr::BVAnd(..) => vtable.and(args[0], args[1], self),
            Expr::BVOr(..) => vtable.or(args[0], args[1], self),
            Expr::BVXor(..) => vtable.xor(args[0], args[1], self),
            Expr::BVEqual(..) => vtable.equal(args[0], args[1], self),
            Expr::BVGreater(..) => vtable.gt(args[0], args[1], self),
            Expr::BVGreaterEqual(..) => vtable.ge(args[0], args[1], self),
            Expr::BVGreaterSigned(..) => vtable.gt_signed(args[0], args[1], self),
            Expr::BVGreaterEqualSigned(..) => vtable.ge_signed(args[0], args[1], self),
            Expr::BVShiftLeft(..) => vtable.shift_left(args[0], args[1], self),
            Expr::BVShiftRight(..) => vtable.shift_right(args[0], args[1], self),
            Expr::BVArithmeticShiftRight(..) => {
                vtable.arithmetic_shift_right(args[0], args[1], self)
            }
            Expr::BVConcat(..) => vtable.concat(args[0], args[1], self),
            Expr::BVImplies(..) => vtable.implies(args[0], args[1], self),
            _ => todo!("{:?}", self.expr_ctx[expr]),
        }
    }
}
