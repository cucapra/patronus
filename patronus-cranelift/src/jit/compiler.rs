// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use super::bv_codegen::{self, iconst, select_container_primitive};
use super::expr_graph::*;
use super::heap::*;
use super::indep_gen::*;
use super::slot::{ExprLedge, StateBuffer};
use super::{JITResult, THIN_BV_MAX_WIDTH, runtime};
use patronus::expr::{self, ForEachChild, TypeCheck};
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

pub(super) const INT_T: cranelift::prelude::Type = types::I64;

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
        input_state_buffer: &StateBuffer,
        output_state_buffer: &StateBuffer,
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
        )
    }

    pub(super) fn compile_batched_expr_eval(
        &mut self,
        expr_ctx: &expr::Context,
        expr_batch: &[expr::ExprRef],
        input_state_buffer: &StateBuffer,
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
        )
    }

    pub(super) fn compile_batched_update_with_output_slots(
        &mut self,
        expr_ctx: &expr::Context,
        expr_batch: &[expr::ExprRef],
        input_state_buffer: &StateBuffer,
        slot_offset: &[usize],
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
            // epilogue
            |batch, mut codegen_ctx| {
                // TODO: this is simply bad data structures
                for ((&expr, &offset), ret_addr) in
                    std::iter::zip(expr_batch.iter().zip(slot_offset), batch)
                {
                    // ret is the ret address
                    let param_offset = offset as u32;

                    // TODO: is this jank or is there really no better way to do this?
                    let output_buffer_address =
                        codegen_ctx.fn_builder.block_params(codegen_ctx.block_id)[1];
                    let data_type = expr.get_type(expr_ctx);
                    let dst_slot = codegen_ctx
                        .fn_builder
                        .ins()
                        .iadd_imm(output_buffer_address, (param_offset * INT_T.bytes()) as i64);
                    try_swap_compiled_code_ret_with_slot(
                        dst_slot,
                        ret_addr,
                        data_type,
                        &mut codegen_ctx.fn_builder,
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
        expr_batch: &[expr::ExprRef],
        input_state_buffer: &StateBuffer,
        codegen_epilogue: F,
    ) -> JITResult<*const u8>
    where
        F: FnOnce(Vec<Value>, CodeGenContext),
    {
        let mut cranelift_ctx = self.module.make_context();
        cranelift_ctx.func.signature = sig;

        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut cranelift_ctx.func, &mut fn_builder_ctx);

        let entry_block = fn_builder.create_block();
        fn_builder.append_block_params_for_function_params(entry_block);
        fn_builder.switch_to_block(entry_block);
        fn_builder.seal_block(entry_block);

        let codegen_ctx = CodeGenContext {
            fn_builder,
            block_id: entry_block,
            expr_ctx,
            expr_batch,
            input_state_buffer,
            compiler: self,
            long_live_cache_read_holes: vec![],
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

pub(super) struct CodeGenContext<'expr, 'ctx, 'engine> {
    pub(super) fn_builder: FunctionBuilder<'ctx>,

    pub(super) expr_ctx: &'expr expr::Context, // TODO: effectively read-only, can be separated
    input_state_buffer: &'engine StateBuffer,  // TODO: effectively used once
    block_id: Block,
    expr_batch: &'engine [expr::ExprRef],
    pub(super) compiler: &'ctx mut JITCompiler,
    /// Points to the dummy instruction that will be replaced with a read instruction from long lived heap resources buffer.
    /// These replacement operations are done after codegen, when the number of long lived cache are determined.
    long_live_cache_read_holes: Vec<(Value, expr::Type)>,
}

impl CodeGenContext<'_, '_, '_> {
    fn codegen<F: FnOnce(Vec<Value>, Self)>(mut self, epilogue: F) {
        let ret = self.mock_interpret();
        self.finalize_long_lived_heap_resources();
        epilogue(ret, self);
    }

    /// returns a vec of addresses of generated functions
    fn mock_interpret(&mut self) -> Vec<Value> {
        let mut evaluated: FxHashMap<expr::ExprRef, TaggedValue> = FxHashMap::default();
        let bottom_up_expr_graph =
            BottomUpExprGraph::from_top_down_graph(self.expr_ctx, self.expr_batch);

        // Track direct depedents of each array related expr node.
        // This allows us to determine whether we could steal heap allocated resources from operand expression.
        let mut array_references: FxHashMap<expr::ExprRef, FxHashSet<expr::ExprRef>> =
            bottom_up_expr_graph
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
        let fringe_compare = |a: &expr::ExprRef, _: &expr::ExprRef| {
            if matches!(self.expr_ctx[*a], expr::Expr::ArrayStore { .. }) {
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
            evaluated.insert(e, self.expr_codegen(e, &arguments));
            arguments.drain(..);
        }
        self.expr_batch.iter().map(|e| *evaluated[e]).collect()
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
                expr::Type::Array(expr::ArrayType {
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
            .iconst(INT_T, src_addr as i64);
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

    pub(super) fn expect_bv_type(&self) -> expr::WidthInt {
        match self.data_type {
            expr::Type::BV(tpe) => tpe,
            _ => panic!("expect bitvec type"),
        }
    }

    pub(super) fn tag(value: Value, data_type: expr::Type) -> Self {
        Self { value, data_type }
    }

    pub(super) fn tag_bv(value: Value, width: expr::WidthInt) -> Self {
        Self::tag(value, expr::Type::BV(width))
    }
}

impl CodeGenContext<'_, '_, '_> {
    /// the meaning of the input state is polymorphic over bv/array
    pub(super) fn load_input_state(&mut self, expr: expr::ExprRef) -> TaggedValue {
        let slot_address = self.input_state_slot(expr);
        let value = self.fn_builder.ins().load(
            INT_T,
            // buffer is allocated by Rust, therefore trusted
            ir::MemFlags::trusted(),
            *slot_address,
            0,
        );
        TaggedValue::tag(value, expr.get_type(self.expr_ctx))
    }

    fn input_state_slot(&mut self, expr: expr::ExprRef) -> TaggedValue {
        let param_offset = self.input_state_buffer.get_state_offset(expr) as u32;
        let input_buffer_address = self.fn_builder.block_params(self.block_id)[0];
        let param_offset = iconst!(self, param_offset * INT_T.bytes());
        let slot_address = self
            .fn_builder
            .ins()
            .iadd(input_buffer_address, param_offset);
        TaggedValue::tag(slot_address, expr.get_type(self.expr_ctx))
    }

    fn expr_codegen(&mut self, expr: expr::ExprRef, args: &[TaggedValue]) -> TaggedValue {
        use expr::Expr;
        let value = match &self.expr_ctx[expr] {
            Expr::BVIte { .. } => {
                assert_eq!(args[1].data_type, args[2].data_type);
                self.fn_builder.ins().select(*args[0], *args[1], *args[2])
            }
            Expr::ArraySymbol { .. }
            | Expr::ArrayConstant { .. }
            | Expr::BVArrayRead { .. }
            | Expr::ArrayStore { .. }
            | Expr::ArrayIte { .. } => {
                // declared new arrays
                panic!("array operations are not supported")
            }

            _ => self.dispatch_bv_operation_codegen(expr, args),
        };
        TaggedValue::tag(value, expr.get_type(self.expr_ctx))
    }

    // dispatch an operation
    fn dispatch_bv_operation_codegen(
        &mut self,
        expr: expr::ExprRef,
        args: &[TaggedValue],
    ) -> Value {
        // args are presumed not to require delegation
        let width = expr.get_bv_type(self.expr_ctx).unwrap();
        if width > 64 {
            panic!("tried to generate code for a bitvec wider than 64b")
        }
        let vtable = bv_codegen::BVWord::new(width);

        use expr::Expr;
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
