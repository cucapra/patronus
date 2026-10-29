// Copyright 2025-2026 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
// author: Willow Ge <lg634@cornell.edu>

use super::JITResult;
use super::bv_codegen;
use super::slot_new::*;
use baa::BitVecOps;
use patronus::expr::{self, TypeCheck};

use cranelift::{codegen::ir, prelude::*};
// a function that evaluates a certain set of expressions
// the pointer argument points to a u64 array containing the state data for the design under simulation.
// this is usually given by StateBuf.as_mut_slice()
pub(super) struct EvalFun(extern "C" fn(*mut u64));

impl EvalFun {
    /// # Safety
    /// caller should guarantee the memory allocated for compiled code has not been reclaimed
    pub(super) unsafe fn call(&self, state_ptr: &mut [u64]) {
        // println!("calling {:?} with {:?}", self.0, state_ptr.as_mut_ptr());
        (self.0)(state_ptr.as_mut_ptr())
    }
}

pub mod module_helpers {

    use crate::jit::{CodeGenContext, expr_graph::BottomUpExprGraph, slot_new::StateBuf};

    use super::JITResult;
    use cranelift::{
        jit::{JITBuilder, JITModule},
        module::Module,
        prelude::*,
    };
    use patronus::expr::{self, ForEachChild, TypeCheck};
    use patronus::system::*;
    use rustc_hash::FxHashMap;

    use super::EvalFun;

    pub fn new_m(flags: Option<&str>) -> JITModule {
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
        let builder = JITBuilder::with_flags(
            &Vec::from_iter(default_flags),
            cranelift::module::default_libcall_names(),
        )
        .unwrap_or_else(|err| panic!("fail to launch jit instance, due to: {err:?}"));

        JITModule::new(builder)
    }

    pub fn compile_transition_sys(
        m: &mut JITModule,
        expr_ctx: &expr::Context,
        sys: &TransitionSystem,
        input_state_buffer: &StateBuf,
        output_state_buffer: &StateBuf,
    ) -> JITResult<EvalFun> {
        let (next_expr_batch, states_expr): (Vec<_>, Vec<_>) = sys
            .states
            .iter()
            .filter_map(|state| state.next.map(|next| (next, state.symbol)))
            .unzip();
        let slot_offset = output_state_buffer.batch_offsets(&states_expr);
        compile_exprs(
            m,
            expr_ctx,
            &next_expr_batch,
            input_state_buffer,
            &slot_offset,
        )
    }

    pub fn compile_expr_batch(
        m: &mut JITModule,
        expr_ctx: &expr::Context,
        expr_batch: &[expr::ExprRef],
        state: &mut StateBuf,
    ) -> JITResult<EvalFun> {
        let slot_offset = state.batch_offsets(expr_batch);
        compile_exprs(m, expr_ctx, expr_batch, state, &slot_offset)
    }

    fn compile_exprs(
        m: &mut JITModule,
        expr_ctx: &expr::Context,
        expr_batch: &[expr::ExprRef],
        input_state_buffer: &StateBuf,
        out_offsets: &[usize],
    ) -> JITResult<EvalFun> {
        assert_eq!(expr_batch.len(), out_offsets.len());
        let sig = Signature {
            params: vec![AbiParam::new(types::I64)],
            returns: vec![],
            call_conv: isa::CallConv::SystemV,
        };
        let mut cranelift_ctx = m.make_context();
        cranelift_ctx.func.signature = sig;

        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let mut fn_builder = FunctionBuilder::new(&mut cranelift_ctx.func, &mut fn_builder_ctx);

        let entry_block = fn_builder.create_block();
        fn_builder.append_block_params_for_function_params(entry_block);
        fn_builder.switch_to_block(entry_block);
        fn_builder.seal_block(entry_block);

        let entry_params = fn_builder.block_params(entry_block);
        let in_addr = entry_params[0];
        let out_addr = entry_params[0];

        let mut codegen_ctx = CodeGenContext {
            fn_builder,
            in_addr,
            out_addr,
            input_state_buffer,
        };

        // keep track of where evaluated expressions store their results
        let mut evaluated: FxHashMap<expr::ExprRef, Value> = FxHashMap::default();
        let bottom_up_expr_graph = BottomUpExprGraph::from_top_down_graph(expr_ctx, expr_batch);

        let mut arguments = Vec::with_capacity(4);
        let walker = bottom_up_expr_graph.walker();
        // walk graph bottom up
        for e in walker {
            // for each expression, generate code. its arguments should be in the evaluated map
            let expr = &expr_ctx[e];
            expr.for_each_child(|child| {
                arguments.push(evaluated[child]);
            });
            let r = codegen_ctx.expr_codegen(e, expr_ctx, &arguments);
            // println!("{:?}", r);
            evaluated.insert(e, r);
            arguments.clear();
        }
        // now, write outputs to the output location
        for (idx, expr) in expr_batch.iter().enumerate() {
            let t = expr.get_type(expr_ctx);
            let loc = evaluated[expr];
            let offset = out_offsets[idx] as u32;
            codegen_ctx.output_state(t, loc, offset);
        }
        codegen_ctx.fn_builder.ins().return_(&[]);
        codegen_ctx.fn_builder.finalize();

        // println!("{}", cranelift_ctx.func);
        // println!("BEGIN FUNC\n {} \n \n", cranelift_ctx.func);

        let function_id = m.declare_anonymous_function(&cranelift_ctx.func.signature)?;
        m.define_function(function_id, &mut cranelift_ctx)?;
        m.clear_context(&mut cranelift_ctx);
        m.finalize_definitions()?;

        let fn_addr = m.get_finalized_function(function_id);

        let res = unsafe {
            // SAFETY: upheld by the unsafeness of call method
            EvalFun(std::mem::transmute::<*const u8, extern "C" fn(*mut u64)>(
                fn_addr,
            ))
        };
        // println!("finished with compilation");
        Ok(res)
    }
}

// essentially wraps the cranelift builder with some information pertinent for the BTOR use case
pub(super) struct CodeGenContext<'ctx, 'engine> {
    pub(super) fn_builder: FunctionBuilder<'ctx>,
    input_state_buffer: &'engine StateBuf,
    in_addr: Value,
    out_addr: Value,
}

macro_rules! iconst {
    ($ctx: expr, $value: expr) => {
        $ctx.fn_builder.ins().iconst(types::I64, ($value) as i64)
    };
}

impl CodeGenContext<'_, '_> {
    /// the meaning of the input state is polymorphic over bv/array
    pub(super) fn load_input_state(
        &mut self,
        expr: expr::ExprRef,
        expr_ctx: &expr::Context,
    ) -> Value {
        let param_offset = self.input_state_buffer.offset_query(expr).unwrap() as u32;
        let offset_const = iconst!(self, param_offset * types::I64.bytes());
        let slot_address = self.fn_builder.ins().iadd(self.in_addr, offset_const);

        let width = expr.get_bv_type(expr_ctx).unwrap();
        self.fn_builder.ins().load(
            bv_codegen::select_container_primitive(width),
            // buffer is allocated by Rust, therefore trusted
            ir::MemFlags::trusted(),
            slot_address,
            0,
        )
    }

    // generate code to perform the final state update for one given state
    fn output_state(&mut self, ty: expr::Type, mut ret_loc: Value, out_offset: u32) {
        let fn_builder = &mut self.fn_builder;
        let dst_slot = fn_builder
            .ins()
            .iadd_imm(self.out_addr, (out_offset * types::I64.bytes()) as i64);
        let type_width = ty.get_bit_vector_width().unwrap();

        // pad if required
        ret_loc = bv_codegen::extend_to_fit(fn_builder, ret_loc, type_width, 64);
        fn_builder
            .ins()
            .store(ir::MemFlags::trusted(), ret_loc, dst_slot, 0);
    }

    // generate code for an expression
    // NOTE: this is kind of non-ideal, preferably find some alternate approach in the future
    pub(super) fn expr_codegen(
        &mut self,
        expr: expr::ExprRef,
        expr_ctx: &expr::Context,
        args: &[Value],
    ) -> Value {
        use bv_codegen::*;
        use expr::Expr;
        let b = &mut self.fn_builder;
        // println!("generating code for {:?} {:?}", expr_ctx[expr], args);

        match expr_ctx[expr] {
            Expr::BVSymbol { .. } => self.load_input_state(expr, expr_ctx),
            Expr::BVLiteral(value) => {
                let v = value.get(expr_ctx);
                literal(b, v, v.width())
            }
            // unary, includes dest width
            Expr::BVNot(_, w) => not(b, args[0], w),
            Expr::BVNegate(_, w) => negate(b, args[0], w),

            // unary, includes source and dest width
            Expr::BVZeroExt { by, width, .. } => zero_extend(b, args[0], by, width),
            Expr::BVSignExt { by, width, .. } => sign_extend(b, args[0], by, width),
            Expr::BVSlice { hi, lo, e } => {
                let v = e.get_bv_type(expr_ctx).unwrap();
                slice(b, args[0], hi, lo, v)
            }

            // binary which don't require width
            Expr::BVEqual(..) => b.ins().icmp(IntCC::Equal, args[0], args[1]),
            Expr::BVGreater(..) => b.ins().icmp(IntCC::UnsignedGreaterThan, args[0], args[1]),
            Expr::BVGreaterEqual(..) => {
                b.ins()
                    .icmp(IntCC::UnsignedGreaterThanOrEqual, args[0], args[1])
            }
            Expr::BVGreaterSigned(..) => b.ins().icmp(IntCC::SignedGreaterThan, args[0], args[1]),
            Expr::BVGreaterEqualSigned(..) => {
                b.ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, args[0], args[1])
            }
            Expr::BVAnd(..) => b.ins().band(args[0], args[1]),
            Expr::BVOr(..) => b.ins().bor(args[0], args[1]),
            Expr::BVXor(..) => b.ins().bxor(args[0], args[1]),

            // doesn't have overflow width, needs it
            Expr::BVImplies(e1, ..) => {
                let out_w = e1.get_bv_type(expr_ctx).unwrap();
                implies(b, args[0], args[1], out_w)
            }

            // binary

            // these require an overflow guard
            Expr::BVAdd(_, _, w) => add(b, args[0], args[1], w),
            Expr::BVSub(_, _, w) => sub(b, args[0], args[1], w),
            Expr::BVMul(_, _, w) => mul(b, args[0], args[1], w),

            Expr::BVShiftLeft(_, _, w) => shift_left(b, args[0], args[1], w),
            Expr::BVShiftRight(_, _, w) => shift_right(b, args[0], args[1], w),
            Expr::BVArithmeticShiftRight(_, _, w) => arithmetic_shift_right(b, args[0], args[1], w),
            Expr::BVConcat(e1, e2, _) => {
                let w1 = e1.get_bv_type(expr_ctx).unwrap();
                let w2 = e2.get_bv_type(expr_ctx).unwrap();
                concat(b, args[0], w1, args[1], w2)
            }

            Expr::BVIte { .. } => b.ins().select(args[0], args[1], args[2]),

            _ => panic!("unsupported op {:?}", expr_ctx[expr]),
        }
    }
}
