// This is another implementation of the JIT compiler
// In this implementation we do not share data between the interpreter and the compiled code
// We do copies before and after the execution

use crate::instructions::*;
use crate::machine::*;
use crate::parser::ast::*;

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, FuncId};
use cranelift_codegen::{ir::stackslot::*, ir::entities::*, Context};
use cranelift::prelude::codegen::ir::immediates::Offset32;

use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum JitCompileError {
    UndefinedPredicate,
    InstructionNotImplemented,
}


pub struct JitMachine {
    trampolines: Vec<*const u8>,
    module: JITModule,
    ctx: Context,
    func_ctx: FunctionBuilderContext,
    vec_as_ptr: *const u8,
    vec_as_ptr_sig: Signature,
    vec_push: *const u8,
    vec_push_sig: Signature,
    vec_len: *const u8,
    vec_len_sig: Signature,
    vec_truncate: *const u8,
    vec_truncate_sig: Signature,
    print_func: FuncId,
    print_func8: FuncId,
    vec_pop: FuncId,
    predicates: HashMap<(String, usize), JitPredicate>,
}

pub struct JitPredicate {
    code_ptr: *const u8,
    func_id: FuncId,
}

impl std::fmt::Debug for JitMachine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "JitMachine")
    }
}


impl JitMachine {
    pub fn new() -> Self {
	let mut builder = JITBuilder::with_flags(&[
	    ("preserve_frame_pointers", "true"),
	    ("enable_llvm_abi_extensions", "1"),
	],
					     cranelift_module::default_libcall_names()
	).unwrap();
	builder.symbol("print_func", print_syscall as *const u8);
	builder.symbol("print_func8", print_syscall8 as *const u8);	
	builder.symbol("vec_pop", vec_pop_syscall as *const u8);
	let mut module = JITModule::new(builder);
	let pointer_type = module.isa().pointer_type();
	let call_conv = module.isa().default_call_conv();

	let mut ctx = module.make_context();
	let mut func_ctx = FunctionBuilderContext::new();
	
	let mut sig = module.make_signature();
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.returns.push(AbiParam::new(types::I8));
	sig.call_conv = call_conv;

	let mut trampolines = vec![];

	// Should be MAX_ARITY
	for n in 0..4 {
	    ctx.func.signature = sig.clone();
	    let mut fn_builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
	    let block = fn_builder.create_block();
	    fn_builder.append_block_params_for_function_params(block);
	    fn_builder.switch_to_block(block);
	    let func_addr = fn_builder.block_params(block)[0];
	    let registers = fn_builder.block_params(block)[1];
	    let heap = fn_builder.block_params(block)[2];
	    let pdl = fn_builder.block_params(block)[3];
	    let stack = fn_builder.block_params(block)[4];
	    let e_pointer = fn_builder.ins().iconst(types::I64, 0);
	    let mut jump_sig = module.make_signature();
	    jump_sig.call_conv = isa::CallConv::Tail;
	    jump_sig.params.push(AbiParam::new(types::I64));
	    jump_sig.params.push(AbiParam::new(types::I64));
	    jump_sig.params.push(AbiParam::new(types::I64));
	    jump_sig.params.push(AbiParam::new(types::I64));
	    let mut params = vec![];
	    params.push(heap);
	    params.push(pdl);
	    params.push(stack);
	    params.push(e_pointer);
	    for i in 1..=n {
		jump_sig.params.push(AbiParam::new(types::I64));
		// jump_sig.returns.push(AbiParam::new(types::I64));
		let reg_value = fn_builder.ins().load(types::I64, MemFlags::trusted(), registers, Offset32::new((i as i32)*8));
		params.push(reg_value);
	    }
	    jump_sig.returns.push(AbiParam::new(types::I8));
	    let jump_sig_ref = fn_builder.import_signature(jump_sig);
	    let jump_call = fn_builder.ins().call_indirect(jump_sig_ref, func_addr, &params);
	    /*for i in 0..n {
		let reg_value = fn_builder.inst_results(jump_call)[i];
		fn_builder.ins().store(MemFlags::trusted(), reg_value, registers, Offset32::new(((i as i32) + 1) * 8));
	}*/
	    let fail = fn_builder.inst_results(jump_call)[0];
	    fn_builder.ins().return_(&[fail]);
	    fn_builder.seal_block(block);
	    fn_builder.finalize();

	    let func = module.declare_function(&format!("$trampoline/{}", n), Linkage::Local, &sig).unwrap();
	    module.define_function(func, &mut ctx).unwrap();
	    // println!("{}", ctx.func.display());
	    module.finalize_definitions().unwrap();	    
	    module.clear_context(&mut ctx);
	    let code_ptr: *const u8 = unsafe { std::mem::transmute(module.get_finalized_function(func)) };	    
	    trampolines.push(code_ptr);
	}

	let mut print_func_sig = module.make_signature();
        print_func_sig.params.push(AbiParam::new(types::I64));
        let print_func = module
            .declare_function("print_func", Linkage::Import, &print_func_sig)
            .unwrap();
	let mut print_func_sig8 = module.make_signature();
        print_func_sig8.params.push(AbiParam::new(types::I8));
        let print_func8 = module
            .declare_function("print_func8", Linkage::Import, &print_func_sig8)
            .unwrap();	
	
	let mut vec_pop_sig = module.make_signature();
	vec_pop_sig.params.push(AbiParam::new(pointer_type));
	vec_pop_sig.returns.push(AbiParam::new(types::I64));
	let vec_pop = module
	    .declare_function("vec_pop", Linkage::Import, &vec_pop_sig)
	    .unwrap();
	
	let vec_as_ptr = Vec::<HeapCellValue>::as_ptr as *const u8;
	let mut vec_as_ptr_sig = module.make_signature();
	vec_as_ptr_sig.params.push(AbiParam::new(pointer_type));
	vec_as_ptr_sig.returns.push(AbiParam::new(pointer_type));
	let vec_push = Vec::<HeapCellValue>::push as *const u8;
	let mut vec_push_sig = module.make_signature();
	vec_push_sig.params.push(AbiParam::new(pointer_type));
	vec_push_sig.params.push(AbiParam::new(types::I64));
	let vec_len = Vec::<HeapCellValue>::len as *const u8;
	let mut vec_len_sig = module.make_signature();
	vec_len_sig.params.push(AbiParam::new(pointer_type));
	vec_len_sig.returns.push(AbiParam::new(types::I64));
	let vec_truncate = Vec::<HeapCellValue>::truncate as *const u8;
	let mut vec_truncate_sig = module.make_signature();
	vec_truncate_sig.params.push(AbiParam::new(pointer_type));
	vec_truncate_sig.params.push(AbiParam::new(types::I64));

	let predicates = HashMap::new();
	JitMachine {
	    trampolines,
	    module,
	    ctx,
	    func_ctx,
	    vec_as_ptr,
	    vec_as_ptr_sig,
	    vec_push,
	    vec_push_sig,
	    vec_len,
	    vec_len_sig,
	    vec_truncate,
	    vec_truncate_sig,
	    print_func,
	    print_func8,
	    vec_pop,
	    predicates
	}
    }

    pub fn compile(&mut self, name: &str, arity: usize, code: Code) -> Result<(), JitCompileError> {

	let mut sig = self.module.make_signature();
	sig.params.push(AbiParam::new(types::I64));
	sig.params.push(AbiParam::new(types::I64));
	sig.params.push(AbiParam::new(types::I64));
	sig.params.push(AbiParam::new(types::I64));
	for _ in 1..=arity {
	    sig.params.push(AbiParam::new(types::I64));
	    // sig.returns.push(AbiParam::new(types::I64));
	}
	sig.returns.push(AbiParam::new(types::I8));
	sig.call_conv = isa::CallConv::Tail;
	self.ctx.func.signature = sig.clone();
	self.ctx.set_disasm(true);

	let mut fn_builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);
	let block = fn_builder.create_block();
	fn_builder.append_block_params_for_function_params(block);
	fn_builder.switch_to_block(block);
	fn_builder.seal_block(block);

	let heap = fn_builder.block_params(block)[0];
	let pdl = fn_builder.block_params(block)[1];
	let stack = fn_builder.block_params(block)[2];
	let e_pointer = fn_builder.block_params(block)[3];
	let mode = Variable::new(0);
	fn_builder.declare_var(mode, types::I8);
	let s = Variable::new(1);
	fn_builder.declare_var(s, types::I64);
	let e = Variable::new(3);
	fn_builder.declare_var(e, types::I64);
	fn_builder.def_var(e, e_pointer);
	
	let mut registers = vec![];
	// TODO: This could be optimized more, we know the maximum register we're using
	for i in 1..MAX_ARITY {
	    if i <= arity {
	        let reg = fn_builder.block_params(block)[i + 3];
	        registers.push(reg);
	    } else {
		let reg = fn_builder.ins().iconst(types::I64, 0);
		registers.push(reg);
	    }
	}

	macro_rules! print_rt {
	    ($x:expr) => {
		{
		    let print_func_fn = self.module.declare_func_in_func(self.print_func, &mut fn_builder.func);
		    fn_builder.ins().call(print_func_fn, &[$x]);
		}
	    }
	}

	macro_rules! print_rt8 {
	    ($x:expr) => {
		{
		    let print_func_fn = self.module.declare_func_in_func(self.print_func8, &mut fn_builder.func);
		    fn_builder.ins().call(print_func_fn, &[$x]);
		}
	    }
	}	

        macro_rules! vec_len {
	    ($x:expr) => {
		{let sig_ref = fn_builder.import_signature(self.vec_len_sig.clone());
		let vec_len_fn = fn_builder.ins().iconst(types::I64, self.vec_len as i64);
		let call_vec_len = fn_builder.ins().call_indirect(sig_ref, vec_len_fn, &[$x]);
		let vec_len = fn_builder.inst_results(call_vec_len)[0];
		 vec_len}
	    }
	}

	macro_rules! vec_pop {
	    ($x:expr) => {
		{
		    let vec_pop_fn = self.module.declare_func_in_func(self.vec_pop, &mut fn_builder.func);
		    let call_vec_pop = fn_builder.ins().call(vec_pop_fn, &[$x]);
		    let value = fn_builder.inst_results(call_vec_pop)[0];
		    value
		}
	    }
	}

	macro_rules! vec_push {
	    ($x:expr, $y:expr) => {
		{
		    let sig_ref = fn_builder.import_signature(self.vec_push_sig.clone());
		    let vec_push_fn = fn_builder.ins().iconst(types::I64, self.vec_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, vec_push_fn, &[$x, $y]);
		}
	    }
	}

	macro_rules! vec_truncate {
	    ($x:expr, $y:expr) => {
		{
		    let sig_ref = fn_builder.import_signature(self.vec_truncate_sig.clone());
		    let vec_truncate_fn = fn_builder.ins().iconst(types::I64, self.vec_truncate as i64);
		    fn_builder.ins().call_indirect(sig_ref, vec_truncate_fn, &[$x, $y]);
		}
	    }
	}

	macro_rules! vec_as_ptr {
	    ($x:expr) => {
		{
		    let sig_ref = fn_builder.import_signature(self.vec_as_ptr_sig.clone());
		    let vec_as_ptr_fn = fn_builder.ins().iconst(types::I64, self.vec_as_ptr as i64);
		    let call_vec_as_ptr = fn_builder.ins().call_indirect(sig_ref, vec_as_ptr_fn, &[$x]);
		    let heap_ptr = fn_builder.inst_results(call_vec_as_ptr)[0];
		    heap_ptr
		}
	    }
	}

	/* STORE is an operation that abstracts the access to a data cell. It can return the data cell itself
	 * or some other data cell if it points to some data cell in the heap
	 */
	macro_rules! store {
	    ($x:expr) => {
		{
		    let merge_block = fn_builder.create_block();
		    fn_builder.append_block_param(merge_block, types::I64);
		    let is_var_block = fn_builder.create_block();
		    fn_builder.append_block_param(is_var_block, types::I64);
		    let is_not_var_block = fn_builder.create_block();
		    fn_builder.append_block_param(is_not_var_block, types::I64);
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    let is_var = fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Var as i64);
		    fn_builder.ins().brif(is_var, is_var_block, &[$x], is_not_var_block, &[$x]);
		    // is_var
		    fn_builder.switch_to_block(is_var_block);
		    fn_builder.seal_block(is_var_block);
		    let param = fn_builder.block_params(is_var_block)[0];
		    let heap_ptr = vec_as_ptr!(heap);
		    let idx = fn_builder.ins().ishl_imm(param, 8);
		    let idx = fn_builder.ins().ushr_imm(idx, 5);
		    let idx = fn_builder.ins().iadd(heap_ptr, idx);
		    let heap_value = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx, Offset32::new(0));
		    fn_builder.ins().jump(merge_block, &[heap_value]);
		    // is_not_var
		    fn_builder.switch_to_block(is_not_var_block);
		    fn_builder.seal_block(is_not_var_block);
		    let param = fn_builder.block_params(is_not_var_block)[0];
		    fn_builder.ins().jump(merge_block, &[param]);
		    // merge
		    fn_builder.switch_to_block(merge_block);
		    fn_builder.seal_block(merge_block);
		    fn_builder.block_params(merge_block)[0]
		}
	    }
	}

	/* DEREF is an operation that follows a chain of REF until arriving at a self-referential REF
	 * (unbounded variable) or something that is not a REF
	 */
	macro_rules! deref {
	    ($x:expr) => {
		{
		    let exit_block = fn_builder.create_block();
		    fn_builder.append_block_param(exit_block, types::I64);
		    let loop_block = fn_builder.create_block();
		    fn_builder.append_block_param(loop_block, types::I64);
		    fn_builder.ins().jump(loop_block, &[$x]);
		    fn_builder.switch_to_block(loop_block);
		    let addr = fn_builder.block_params(loop_block)[0];
		    let value = store!(addr);
		    // check if is var
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    let is_var = fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Var as i64);
		    let not_equal = fn_builder.ins().icmp(IntCC::NotEqual, value, addr);
		    let check = fn_builder.ins().band(is_var, not_equal);
		    fn_builder.ins().brif(check, loop_block, &[value], exit_block, &[value]);
		    // exit
		    fn_builder.seal_block(loop_block);
		    fn_builder.seal_block(exit_block);
		    fn_builder.switch_to_block(exit_block);
		    fn_builder.block_params(exit_block)[0]
		    
		}
	    }
	}

	/* BIND is an operation that takes two data cells, one of them being an unbounded REF / Var
	 * and makes that REF point the other cell on the heap
	 */
	macro_rules! bind {
	    ($x:expr, $y:expr) => {
		{
		    let first_var_block = fn_builder.create_block();
		    let else_first_var_block = fn_builder.create_block();
		    let exit_block = fn_builder.create_block();
		    let heap_ptr = vec_as_ptr!(heap);		    
		    // check if x is var
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    let is_var = fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Var as i64);
		    fn_builder.ins().brif(is_var, first_var_block, &[], else_first_var_block, &[]);
		    // first var block
		    fn_builder.seal_block(first_var_block);
		    fn_builder.seal_block(else_first_var_block);
		    fn_builder.switch_to_block(first_var_block);
    		    // The order of HeapCellValue is TAG (6), M (1), F (1), VALUE (56)
		    let idx = fn_builder.ins().ishl_imm($x, 8);
		    let idx = fn_builder.ins().ushr_imm(idx, 5);
		    let idx = fn_builder.ins().iadd(heap_ptr, idx);
		    fn_builder.ins().store(MemFlags::trusted(), $y, idx, Offset32::new(0));
		    fn_builder.ins().jump(exit_block, &[]);
		    // else_first_var_block
		    // suppose the other cell is a var
		    fn_builder.switch_to_block(else_first_var_block);
		    let idx = fn_builder.ins().ishl_imm($y, 8);
		    let idx = fn_builder.ins().ushr_imm(idx, 5);
		    let idx = fn_builder.ins().iadd(heap_ptr, idx);
		    fn_builder.ins().store(MemFlags::trusted(), $x, idx, Offset32::new(0));
		    fn_builder.ins().jump(exit_block, &[]);		    
		    // exit
		    fn_builder.seal_block(exit_block);
		    fn_builder.switch_to_block(exit_block);
		}
	    }
	}

	macro_rules! is_var {
	    ($x:expr) => {
		{
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Var as i64)
		}
	    }
	}

	macro_rules! is_str {
	    ($x:expr) => {
		{
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Str as i64)
		}
	    }
	}

	macro_rules! unify {
	    ($x:expr, $y:expr) => {
		{
		    let exit = fn_builder.create_block();
		    fn_builder.append_block_param(exit, types::I8);

		    // start unification
		    vec_push!(pdl, $x);
		    vec_push!(pdl, $y);
		    let pdl_size = fn_builder.ins().iconst(types::I64, 2);
		    let fail_status = fn_builder.ins().iconst(types::I8, 0);

		    let pre_loop_block = fn_builder.create_block();
		    fn_builder.append_block_param(pre_loop_block, types::I64); // pdl_size
		    fn_builder.append_block_param(pre_loop_block, types::I8); // fail_status
		    fn_builder.ins().jump(pre_loop_block, &[pdl_size, fail_status]);
		    fn_builder.switch_to_block(pre_loop_block);
		    // pre_loop_block
		    let pdl_size = fn_builder.block_params(pre_loop_block)[0];
		    let fail_status = fn_builder.block_params(pre_loop_block)[1];
		    let pdl_size_is_zero = fn_builder.ins().icmp_imm(IntCC::Equal, pdl_size, 0);
		    let fail_status_is_true = fn_builder.ins().icmp_imm(IntCC::NotEqual, fail_status, 0);
		    let loop_check = fn_builder.ins().bor(pdl_size_is_zero, fail_status_is_true);
    		    let loop_block = fn_builder.create_block();	
		    fn_builder.append_block_param(loop_block, types::I64); // pdl_size
		    fn_builder.append_block_param(loop_block, types::I8); // fail_status	    

		    fn_builder.ins().brif(loop_check, exit, &[fail_status], loop_block, &[pdl_size, fail_status]);
		    fn_builder.seal_block(exit);		    
		    fn_builder.seal_block(loop_block);
		    fn_builder.switch_to_block(loop_block);
		    // loop_block
		    let pdl_size = fn_builder.block_params(loop_block)[0];
		    let fail_status = fn_builder.block_params(loop_block)[1];
		    let d1 = vec_pop!(pdl);
		    let d2 = vec_pop!(pdl);
		    let d1 = deref!(d1);
		    let d2 = deref!(d2);
		    let pdl_size = fn_builder.ins().iadd_imm(pdl_size, -2);
		    let are_equal = fn_builder.ins().icmp(IntCC::Equal, d1, d2);
		    let unify_two_unequal_cells = fn_builder.create_block();
		    fn_builder.append_block_param(unify_two_unequal_cells, types::I64);
		    fn_builder.append_block_param(unify_two_unequal_cells, types::I8);		    
		    
		    fn_builder.ins().brif(are_equal, pre_loop_block, &[pdl_size, fail_status], unify_two_unequal_cells, &[pdl_size, fail_status]);
		    fn_builder.seal_block(unify_two_unequal_cells);

		    // unify_two_unequal_cells
		    fn_builder.switch_to_block(unify_two_unequal_cells);
		    let pdl_size = fn_builder.block_params(unify_two_unequal_cells)[0];
		    let fail_status = fn_builder.block_params(unify_two_unequal_cells)[1];
		    let is_var_d1 = is_var!(d1);
		    let is_var_d2 = is_var!(d2);
		    let any_is_var = fn_builder.ins().bor(is_var_d1, is_var_d2);
		    let bind_var = fn_builder.create_block();
		    fn_builder.append_block_param(bind_var, types::I64);
		    fn_builder.append_block_param(bind_var, types::I8);
		    let unify_str = fn_builder.create_block();
		    fn_builder.append_block_param(unify_str, types::I64);
		    fn_builder.append_block_param(unify_str, types::I8);
		    fn_builder.ins().brif(any_is_var, bind_var, &[pdl_size, fail_status], unify_str, &[pdl_size, fail_status]);
		    fn_builder.seal_block(bind_var);
		    fn_builder.seal_block(unify_str);

		    // bind_var
		    fn_builder.switch_to_block(bind_var);
		    let pdl_size = fn_builder.block_params(bind_var)[0];
		    let fail_status = fn_builder.block_params(bind_var)[1];		    
		    bind!(d1, d2);
		    fn_builder.ins().jump(pre_loop_block, &[pdl_size, fail_status]);

		    // unify_str
		    fn_builder.switch_to_block(unify_str);
		    let pdl_size = fn_builder.block_params(unify_str)[0];
		    let fail_status = fn_builder.block_params(unify_str)[1];
		    let heap_ptr = vec_as_ptr!(heap);
		    let idx1 = fn_builder.ins().ishl_imm(d1, 8);
		    let idx1 = fn_builder.ins().ushr_imm(idx1, 5);
		    let idx1 = fn_builder.ins().iadd(heap_ptr, idx1);
		    let d1 = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx1, Offset32::new(0));
		    let idx2 = fn_builder.ins().ishl_imm(d2, 8);
		    let idx2 = fn_builder.ins().ushr_imm(idx2, 5);
		    let idx2 = fn_builder.ins().iadd(heap_ptr, idx2);
		    let d2 = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx2, Offset32::new(0));
		    let are_atom_arity_equal = fn_builder.ins().icmp(IntCC::Equal, d1, d2);
		    let fail_status_bad = fn_builder.ins().iconst(types::I8, 1);
		    let pre_push_subterms = fn_builder.create_block();
		    fn_builder.append_block_param(pre_push_subterms, types::I64);		    
		    fn_builder.append_block_param(pre_push_subterms, types::I64);
		    fn_builder.append_block_param(pre_push_subterms, types::I8);
		    let arity = fn_builder.ins().ishl_imm(d1, 8);
		    let arity = fn_builder.ins().ushr_imm(arity, 54);
		    fn_builder.ins().brif(are_atom_arity_equal, pre_push_subterms, &[arity, pdl_size, fail_status], pre_loop_block, &[pdl_size, fail_status_bad]);

		    // pre_push_subterms
		    fn_builder.switch_to_block(pre_push_subterms);
		    let arity = fn_builder.block_params(pre_push_subterms)[0];
		    let pdl_size = fn_builder.block_params(pre_push_subterms)[1];
		    let fail_status = fn_builder.block_params(pre_push_subterms)[2];
		    let zero_remaining = fn_builder.ins().icmp_imm(IntCC::Equal, arity, 0);
		    let push_subterms = fn_builder.create_block();
		    fn_builder.append_block_param(push_subterms, types::I64);		    
		    fn_builder.append_block_param(push_subterms, types::I64);
		    fn_builder.append_block_param(push_subterms, types::I8);		    
		    fn_builder.ins().brif(zero_remaining, pre_loop_block, &[pdl_size, fail_status], push_subterms, &[arity, pdl_size, fail_status]);
		    fn_builder.seal_block(pre_loop_block);
		    fn_builder.seal_block(push_subterms);
		    // push_subterms
		    fn_builder.switch_to_block(push_subterms);
		    let d1_next = fn_builder.ins().iadd_imm(idx1, 8);
		    let d1_next = fn_builder.ins().iadd(heap_ptr, d1_next);
		    let d1_next = fn_builder.ins().load(types::I64, MemFlags::trusted(), d1_next, Offset32::new(0));
		    vec_push!(pdl, d1_next);
		    let d2_next = fn_builder.ins().iadd_imm(idx2, 8);
		    let d2_next = fn_builder.ins().iadd(heap_ptr, d2_next);
    		    let d2_next = fn_builder.ins().load(types::I64, MemFlags::trusted(), d2_next, Offset32::new(0));
		    vec_push!(pdl, d2_next);
		    let pdl_size = fn_builder.ins().iadd_imm(pdl_size, 2);
		    let arity = fn_builder.ins().iadd_imm(arity, -1);
		    fn_builder.ins().jump(pre_push_subterms, &[arity, pdl_size, fail_status]);
		    fn_builder.seal_block(pre_push_subterms);
		    
		    // exit
		    fn_builder.switch_to_block(exit);
		    let fail_status = fn_builder.block_params(exit)[0];
		    let exit_early = fn_builder.create_block();
		    let exit_normal = fn_builder.create_block();
		    fn_builder.ins().brif(fail_status, exit_early, &[], exit_normal, &[]);
		    fn_builder.seal_block(exit_early);
		    fn_builder.seal_block(exit_normal);
		    fn_builder.switch_to_block(exit_early);
		    fn_builder.ins().return_(&[fail_status]);
		    fn_builder.switch_to_block(exit_normal);
		}
	    }
	}

	macro_rules! read_reg {
	    ($x:expr) => {
		{
                    match $x {
			RegType::Temp(x) => {
			    registers[x-1]
			}
			RegType::Perm(y) => {
			    let idy = ((y as i32) + 1) * 8;
			    let stack_frame = fn_builder.use_var(e);
			    fn_builder.ins().load(types::I64, MemFlags::trusted(), stack_frame, Offset32::new(idy))
			}
		    }
		}
	    }
	}

	macro_rules! write_reg {
	    ($x:expr, $y:expr) => {
		match $x {
		    RegType::Temp(x) => {
			registers[x-1] = $y;
		    }
		    RegType::Perm(y) => {
			let idy = ((y as i32) + 1) * 8;
			let stack_frame = fn_builder.use_var(e);
			fn_builder.ins().store(MemFlags::trusted(), $y, stack_frame, Offset32::new(idy));
		    }
		}
	    }
	}

	for wam_instr in code {
	    match wam_instr {
		/* put_structure is an instruction that puts a new STR in the heap
		 * (STR cell, plus functor + arity cell)
		 * It also saves the STR cell into a register
		 */
		Instruction::PutStructure(name, arity, reg) => {
		    let str_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(str_loc_as_cell!(0).into_bytes()));
		    let vec_len = vec_len!(heap);
		    let str_loc = fn_builder.ins().iadd_imm(vec_len, 1);
		    let str_cell = fn_builder.ins().bor(str_loc, str_cell);
		    
		    let atom_cell = atom_as_cell!(name, arity);
		    let atom = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(atom_cell.into_bytes()));
		    vec_push!(heap, str_cell);
		    vec_push!(heap, atom);

		    write_reg!(reg, str_cell);
		}
		/* set_variable is an instruction that creates a new self-referential REF
		 * (unbounded variable) in the heap and saves that into a register
		 */
		Instruction::SetVariable(reg) => {
		    let heap_loc_cell = heap_loc_as_cell!(0);
		    let heap_loc_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(heap_loc_cell.into_bytes()));
		    let vec_len = vec_len!(heap);
		    let heap_loc_cell = fn_builder.ins().bor(vec_len, heap_loc_cell);
		    vec_push!(heap, heap_loc_cell);
		    write_reg!(reg, heap_loc_cell);
		}
		/* set_value is an instruction that pushes a new data cell from a register to the heap
		 */
		Instruction::SetValue(reg) => {
		    let value = read_reg!(reg);
		    let value = store!(value);
		    vec_push!(heap, value);
		}
		/* get_structure is an instruction that either matches an existing STR or starts writing a new
		 * STR into the heap. If the cell passed via register is an unbounded REF, we start WRITE mode
		 * and unify_variable, unify_value behave similar to set_variable, set_value.
		 * If it's an existing STR, we check functor and arity, set S pointer and start READ mode,
		 * in that mod unify_variable and unify_value will follow the unification procedure
		 */
		Instruction::GetStructure(_lvl, name, arity, reg) => {
		    let xi = read_reg!(reg);
		    let deref = deref!(xi);
		    let store = store!(deref);

		    let is_var_block = fn_builder.create_block();
		    let else_is_var_block = fn_builder.create_block();
		    let is_str_block = fn_builder.create_block();
		    let start_read_mode_block = fn_builder.create_block();
		    let fail_block = fn_builder.create_block();
		    let exit_block = fn_builder.create_block();
		    let is_var = is_var!(store);

		    fn_builder.ins().brif(is_var, is_var_block, &[], else_is_var_block, &[]);
		    fn_builder.seal_block(is_var_block);
		    fn_builder.seal_block(else_is_var_block);
		    // is_var_block
		    fn_builder.switch_to_block(is_var_block);
		    let sig_ref = fn_builder.import_signature(self.vec_push_sig.clone());
		    let vec_push_fn = fn_builder.ins().iconst(types::I64, self.vec_push as i64);		    
		    let str_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(str_loc_as_cell!(0).into_bytes()));
		    let vec_len = vec_len!(heap);
		    let str_cell = fn_builder.ins().bor(vec_len, str_cell);
		    let atom_cell = atom_as_cell!(name, arity);
		    let atom = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(atom_cell.into_bytes()));
		    fn_builder.ins().call_indirect(sig_ref, vec_push_fn, &[heap, atom]);
		    bind!(store, str_cell);
		    let mode_value = fn_builder.ins().iconst(types::I8, 1);
		    fn_builder.def_var(mode, mode_value);
		    fn_builder.ins().jump(exit_block, &[]);

		    // else_is_var_block
		    fn_builder.switch_to_block(else_is_var_block);
		    let is_str = is_str!(store);
		    fn_builder.ins().brif(is_str, is_str_block, &[], fail_block, &[]);
		    fn_builder.seal_block(is_str_block);

		    // is_str_block
		    fn_builder.switch_to_block(is_str_block);
		    let atom = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(atom_cell.into_bytes()));
    		    let heap_ptr = vec_as_ptr!(heap);
		    let idx = fn_builder.ins().ishl_imm(store, 8);
		    let idx = fn_builder.ins().ushr_imm(idx, 5);
		    let idx = fn_builder.ins().iadd(heap_ptr, idx);
		    let heap_value = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx, Offset32::new(0));
		    let result = fn_builder.ins().icmp(IntCC::Equal, heap_value, atom);
		    fn_builder.ins().brif(result, start_read_mode_block, &[], fail_block, &[]);
		    fn_builder.seal_block(start_read_mode_block);
    		    fn_builder.seal_block(fail_block);

		    // start_read_mode_block
		    fn_builder.switch_to_block(start_read_mode_block);
		    let s_ptr = fn_builder.ins().iadd_imm(idx, 8);
		    fn_builder.def_var(s, s_ptr);
		    let mode_value = fn_builder.ins().iconst(types::I8, 0);
		    fn_builder.def_var(mode, mode_value);
		    fn_builder.ins().jump(exit_block, &[]);

		    // fail_block
		    fn_builder.switch_to_block(fail_block);
		    let fail_value = fn_builder.ins().iconst(types::I8, 1);
		    fn_builder.ins().return_(&[fail_value]);

		    // exit_block
		    fn_builder.seal_block(exit_block);
		    fn_builder.switch_to_block(exit_block);
		    
		}
		// TODO: Missing support for PStr and CStr
		/* unify_variable is an instruction that in WRITE mode is identical to set_variable but
		 * in READ mode it reads the data cell from the S pointer to a register
		 */
		Instruction::UnifyVariable(reg) => {
		    let read_block = fn_builder.create_block();
		    let write_block = fn_builder.create_block();
		    let exit_block = fn_builder.create_block();
		    let mode_value = fn_builder.use_var(mode);
		    fn_builder.ins().brif(mode_value, write_block, &[], read_block, &[]);
		    fn_builder.seal_block(read_block);
		    fn_builder.seal_block(write_block);
		    // read
		    fn_builder.switch_to_block(read_block);
		    let s_value = fn_builder.use_var(s);
		    let value = fn_builder.ins().load(types::I64, MemFlags::trusted(), s_value, Offset32::new(0));
		    let value = deref!(value);
		    write_reg!(reg, value);
		    let sum_s = fn_builder.ins().iadd_imm(s_value, 8);
		    fn_builder.def_var(s, sum_s);
		    fn_builder.ins().jump(exit_block, &[]);
		    // write (equal to SetVariable)
		    fn_builder.switch_to_block(write_block);
		    let heap_loc_cell = heap_loc_as_cell!(0);
		    let heap_loc_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(heap_loc_cell.into_bytes()));
		    let vec_len = vec_len!(heap);
		    let heap_loc_cell = fn_builder.ins().bor(vec_len, heap_loc_cell);
		    vec_push!(heap, heap_loc_cell);
		    write_reg!(reg, heap_loc_cell);
		    fn_builder.ins().jump(exit_block, &[]);
		    // exit
		    fn_builder.switch_to_block(exit_block);
		    fn_builder.seal_block(exit_block);
		    
		}
		/* unify_value is an instruction that on WRITE mode behaves like set_value, and in READ mode
		 * executes unification
		 */
		Instruction::UnifyValue(reg) => {
		    let reg = read_reg!(reg);
    		    let read_block = fn_builder.create_block();
		    let write_block = fn_builder.create_block();
		    let exit_block = fn_builder.create_block();
		    let mode_value = fn_builder.use_var(mode);
		    fn_builder.ins().brif(mode_value, write_block, &[], read_block, &[]);
		    fn_builder.seal_block(read_block);
		    fn_builder.seal_block(write_block);
		    // read
		    fn_builder.switch_to_block(read_block);
		    let s_value = fn_builder.use_var(s);
		    let value = fn_builder.ins().load(types::I64, MemFlags::trusted(), s_value, Offset32::new(0));
		    unify!(reg, value);
		    let s_value  = fn_builder.ins().iadd_imm(s_value, 8);
		    fn_builder.def_var(s, s_value);
		    fn_builder.ins().jump(exit_block, &[]);
		    // write
		    fn_builder.switch_to_block(write_block);
		    vec_push!(heap, reg);
		    fn_builder.ins().jump(exit_block, &[]);
		    fn_builder.seal_block(exit_block);

		    // exit
		    fn_builder.switch_to_block(exit_block);
		    
		}
		/* put_variable works similar to set_variable, but it stores the cell in two registers,
		 * Xi normal register and Ai argument register
		 */
		Instruction::PutVariable(reg, arg) => {
		    let heap_loc_cell = heap_loc_as_cell!(0);
		    let heap_loc_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(heap_loc_cell.into_bytes()));
		    let vec_len = vec_len!(heap);
		    let heap_loc_cell = fn_builder.ins().bor(vec_len, heap_loc_cell);
		    vec_push!(heap, heap_loc_cell);
		    write_reg!(reg, heap_loc_cell);
		    registers[arg - 1] = heap_loc_cell;
		}
		/* put_value moves the content from Xi to Ai
		 */
		Instruction::PutValue(reg, arg) => {
		    registers[arg - 1] = read_reg!(reg);
		}
		/* get_variable moves the content from Ai to Xi
		 */
		Instruction::GetVariable(reg, arg) => {
		    write_reg!(reg, registers[arg - 1]);
		}
		/* get_value perform unification between Xi and Ai
		 */
		Instruction::GetValue(reg1, reg2) => {
		    let reg1 = read_reg!(reg1);
		    let reg2 = registers[reg2 - 1];
		    unify!(reg1, reg2);
		}
		/* call executes another predicate in a normal way. It passes all the argument registers
		 * as function arguments
		 */
		Instruction::CallNamed(arity, name, _ ) => {
let Some(predicate) = self.predicates.get(&(name.as_str().to_string(), arity)) else {
			return Err(JitCompileError::UndefinedPredicate);
};
		    let e_value = fn_builder.use_var(e);
		    let func = self.module.declare_func_in_func(predicate.func_id, fn_builder.func);
		    let mut args = vec![];
		    args.push(heap);
		    args.push(pdl);
		    args.push(stack);
		    args.push(e_value);
		    for i in 1..=arity {
			args.push(registers[i-1]);
		    }
		    let call = fn_builder.ins().call(func, &args);
		    let fail_status = fn_builder.inst_results(call)[0];
		    let exit_early = fn_builder.create_block();
		    let resume = fn_builder.create_block();
		    fn_builder.ins().brif(fail_status, exit_early, &[], resume, &[]);
		    fn_builder.seal_block(exit_early);
		    fn_builder.seal_block(resume);
		    fn_builder.switch_to_block(exit_early);
    		    fn_builder.ins().return_(&[fail_status]);
		    fn_builder.switch_to_block(resume);
		}
		/* execute does a tail call instead of a normal call
		 */
		Instruction::ExecuteNamed(arity, name, _) => {
		    let Some(predicate) = self.predicates.get(&(name.as_str().to_string(), arity)) else {
			return Err(JitCompileError::UndefinedPredicate);
		    };
		    let e_value = fn_builder.use_var(e);
		    let func = self.module.declare_func_in_func(predicate.func_id, fn_builder.func);
		    let mut args = vec![];
		    args.push(heap);
		    args.push(pdl);
		    args.push(stack);
		    args.push(e_value);
		    for i in 1..=arity {
			args.push(registers[i-1]);
		    }
		    fn_builder.ins().return_call(func, &args);
		}
		/* allocate creates a new environment frame (ANDFrame). Every frame contains a pointer
		 * to the previous frame start, the continuation pointer (in this case we do not store it
		 * as we have a tree of calls with Cranelift managing this for us), the number of permanent
		 * variables and the permanent variables themselves.
		 */
		Instruction::Allocate(n) => {
		    let new_e_value = vec_len!(stack);
		    let stack_ptr = vec_as_ptr!(stack);
		    let new_e_value = fn_builder.ins().imul_imm(new_e_value, 8);
		    let new_e_value = fn_builder.ins().iadd(stack_ptr, new_e_value);
		    let e_value = fn_builder.use_var(e);
		    vec_push!(stack, e_value);
		    let n_value = fn_builder.ins().iconst(types::I64, n as i64);
		    vec_push!(stack, n_value);
		    let zero = fn_builder.ins().iconst(types::I64, 0);
		    for _ in 0..n {
			vec_push!(stack, zero);
		    }
		    fn_builder.def_var(e, new_e_value);
		}
		/* deallocate restores the previous frame, freeing the current frame
		 */
	        Instruction::Deallocate => {
		    let e_value = fn_builder.use_var(e);
		    let allocated = fn_builder.ins().load(types::I64, MemFlags::trusted(), e_value, Offset32::new(8));
		    let allocated = fn_builder.ins().iadd_imm(allocated, 2);
		    let new_e_value = fn_builder.ins().load(types::I64, MemFlags::trusted(), e_value, Offset32::new(0));
		    let stack_len = vec_len!(stack);
		    let new_stack_len = fn_builder.ins().isub(stack_len, allocated);
		    vec_truncate!(stack, new_stack_len);
		    fn_builder.def_var(e, new_e_value);
		}
		// TODO: manage NonVar cases
		// TODO: Manage unification case
		// TODO: manage STORE[addr] is not REF
		Instruction::GetConstant(_, c, reg) => {
		    let value = read_reg!(reg);
		    let value = deref!(value);
		    let value = store!(value);
		    // The order of HeapCellValue is TAG (6), M (1), F (1), VALUE (56)
		    let c = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(c.into_bytes()));
		    bind!(value, c);
		}
		Instruction::Proceed => {
		    // do we really need to return registers?
		    //fn_builder.ins().return_(&registers[0..arity]);
		    let fail_value = fn_builder.ins().iconst(types::I8, 0);
		    // if we exit here, it's because it succeeded
		    fn_builder.ins().return_(&[fail_value]);
		    break;
	        },
	        _ => {
		    dbg!(wam_instr);
		    fn_builder.finalize();
	            self.module.clear_context(&mut self.ctx);	
		    return Err(JitCompileError::InstructionNotImplemented);
	        }
	    }
	}
	fn_builder.seal_all_blocks();
	fn_builder.finalize();

	let func_id = self.module.declare_function(&format!("{}/{}", name, arity), Linkage::Local, &sig).unwrap();
	self.module.define_function(func_id, &mut self.ctx).unwrap();
	println!("{}", self.ctx.func.display());
	self.module.finalize_definitions().unwrap();	
	let code_ptr = self.module.get_finalized_function(func_id);
	self.predicates.insert((name.to_string(), arity), JitPredicate {
	    code_ptr,
	    func_id
	});
	println!("{}", self.ctx.compiled_code().unwrap().vcode.clone().unwrap());
	self.module.clear_context(&mut self.ctx);
	Ok(())
    }

    pub fn exec(&self, name: &str, arity: usize, machine_st: &mut MachineState) -> Result<(), ()> {
	let Some(predicate) = self.predicates.get(&(name.to_string(), arity)) else {
	    return Err(());
	};
	let trampoline: extern "C" fn (*const u8, *mut Registers, *const Vec<HeapCellValue>, *const Vec<HeapCellValue>, *const Vec<i64>) -> u8 = unsafe { std::mem::transmute(self.trampolines[arity])};
	let registers = machine_st.registers.as_ptr() as *mut Registers;
	let heap = &machine_st.heap as *const Vec<HeapCellValue>;
	let pdl = &machine_st.pdl as *const Vec<HeapCellValue>;
	let stack_vec: Vec<i64> = Vec::with_capacity(1024);
	let stack = &stack_vec as *const Vec<i64>;
	let fail = trampoline(predicate.code_ptr, registers, heap, pdl, stack);
	machine_st.p = machine_st.cp;
	machine_st.fail = if fail == 1 {
	    true
	} else {
	    false
	};
	Ok(())
    }
}


fn print_syscall(value: i64) {
    println!("{}", value);
}

fn print_syscall8(value: i8) {
    println!("{}", value);
}

fn vec_pop_syscall(value: &mut Vec<HeapCellValue>) -> HeapCellValue {
    value.pop().unwrap()
}


#[test]
fn test_put_structure() {
    let code = vec![
	Instruction::PutStructure(atom!("f"), 2, RegType::Temp(1)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_put_structure", 1, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_put_structure", 1, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 2));
    // machine_st_expected.registers[1] = str_loc_as_cell!(0);
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    // assert_eq!(machine_st.registers, machine_st_expected.registers);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_set_variable() {
    let code = vec![
	Instruction::SetVariable(RegType::Temp(1)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_set_variable", 1, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_set_variable", 1, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(heap_loc_as_cell!(0));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    // assert_eq!(machine_st.registers, machine_st_expected.registers);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_set_value() {
    let code = vec![
	Instruction::SetValue(RegType::Temp(1)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_set_value", 1, code).unwrap();
    let mut machine_st = MachineState::new();
    machine_st.registers[1] = atom_as_cell!(atom!("a"), 0);
    jit.exec("test_set_value", 1, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(atom_as_cell!(atom!("a"), 0));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_fig23_wambook() {
    let code = vec![
	Instruction::PutStructure(atom!("h"), 2, RegType::Temp(3)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::SetVariable(RegType::Temp(5)),
	Instruction::PutStructure(atom!("f"), 1, RegType::Temp(4)),
	Instruction::SetValue(RegType::Temp(5)),
	Instruction::PutStructure(atom!("p"), 3, RegType::Temp(1)),
	Instruction::SetValue(RegType::Temp(2)),
	Instruction::SetValue(RegType::Temp(3)),
	Instruction::SetValue(RegType::Temp(4)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_fig23_wambook", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_fig23_wambook", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("h"), 2));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    machine_st_expected.heap.push(heap_loc_as_cell!(3));
    machine_st_expected.heap.push(str_loc_as_cell!(5));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(3));
    machine_st_expected.heap.push(str_loc_as_cell!(8));
    machine_st_expected.heap.push(atom_as_cell!(atom!("p"), 3));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(str_loc_as_cell!(5));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_get_structure_read() {
    let code = vec![
	Instruction::PutStructure(atom!("f"), 1, RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_get_structure", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_get_structure", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_get_structure_write() {
    let code = vec![
	Instruction::SetVariable(RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_get_structure", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_get_structure", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(2));
    machine_st_expected.heap.push(heap_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_get_structure_read_fail() {
    let code = vec![
	Instruction::PutStructure(atom!("h"), 1, RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_get_structure", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_get_structure", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("h"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, true);
}

#[test]
fn test_unify_variable_write() {
    let code = vec![
	Instruction::SetVariable(RegType::Temp(1)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::UnifyVariable(RegType::Temp(2)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_variable_write", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_variable_write", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_unify_value_write() {
    let code = vec![
	Instruction::SetVariable(RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::UnifyValue(RegType::Temp(2)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_write", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_write", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(2));
    machine_st_expected.heap.push(heap_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(1));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_unify_value_read_str() {
    let code = vec![
	Instruction::PutStructure(atom!("f"), 1, RegType::Temp(1)),
	Instruction::PutStructure(atom!("h"), 0, RegType::Temp(2)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(3)),
	Instruction::UnifyValue(RegType::Temp(3)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_read", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_read", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(str_loc_as_cell!(3));    
    machine_st_expected.heap.push(atom_as_cell!(atom!("h"), 0));
    machine_st_expected.heap.push(str_loc_as_cell!(3));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_unify_value_read_str_2() {
    let code = vec![
	Instruction::PutStructure(atom!("f"), 0, RegType::Temp(1)),
	Instruction::PutStructure(atom!("f"), 0, RegType::Temp(2)),
	Instruction::GetValue(RegType::Temp(1), 2),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_read", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_read", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 0));
    machine_st_expected.heap.push(str_loc_as_cell!(3));    
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 0));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);

}

#[test]
fn test_unify_value_read_str_3() {
    let code = vec![
	Instruction::PutStructure(atom!("f"), 1, RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::SetVariable(RegType::Temp(3)),
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::UnifyValue(RegType::Temp(3)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_read", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_read", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(3));
    machine_st_expected.heap.push(heap_loc_as_cell!(3));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);

}


#[test]
fn test_unify_value_1() {
    let code = vec![
	Instruction::SetVariable(RegType::Temp(1)),
	Instruction::GetValue(RegType::Temp(1), 1),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_read", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_read", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(heap_loc_as_cell!(0));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}


#[test]
fn test_unify_value_2() {
    let code = vec![
	Instruction::SetVariable(RegType::Temp(1)),
	Instruction::SetVariable(RegType::Temp(2)),
	Instruction::GetValue(RegType::Temp(1), 2),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_read", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_read", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(heap_loc_as_cell!(0));
    machine_st_expected.heap.push(heap_loc_as_cell!(0));    
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}


#[test]
fn test_unify_value_read_fail() {
    let code = vec![
	Instruction::PutStructure(atom!("h"), 0, RegType::Temp(2)),
	Instruction::PutStructure(atom!("z"), 0, RegType::Temp(3)),	
	Instruction::PutStructure(atom!("f"), 1, RegType::Temp(1)),
	Instruction::SetValue(RegType::Temp(2)),
	Instruction::SetValue(RegType::Temp(3)),	
	Instruction::GetStructure(Level::Shallow, atom!("f"), 1, RegType::Temp(1)),
	Instruction::UnifyValue(RegType::Temp(3)),
	Instruction::Proceed
    ];
    let mut jit = JitMachine::new();
    jit.compile("test_unify_value_read", 0, code).unwrap();
    let mut machine_st = MachineState::new();
    jit.exec("test_unify_value_read", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(atom_as_cell!(atom!("h"), 0));
    machine_st_expected.heap.push(str_loc_as_cell!(3));
    machine_st_expected.heap.push(atom_as_cell!(atom!("z"), 0));
    machine_st_expected.heap.push(str_loc_as_cell!(5));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(str_loc_as_cell!(1));
    machine_st_expected.heap.push(str_loc_as_cell!(3));    
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, true);
}

#[test]
fn test_execute_named() {
    let mut machine_st = MachineState::new();    
    let code_b = vec![
	Instruction::GetConstant(Level::Shallow, atom_as_cell!(atom!("f"), 0), RegType::Temp(1)),
	Instruction::Proceed
    ];
    let code_a = vec![
	Instruction::PutVariable(RegType::Temp(1), 1),
	Instruction::ExecuteNamed(1, atom!("b"), CodeIndex::default(&mut machine_st.arena)),
    ];
    let mut jit = JitMachine::new();
    jit.compile("b", 1, code_b).unwrap();
    jit.compile("a", 0, code_a).unwrap();
    jit.exec("a", 0, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 0));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
}

#[test]
fn test_allocate() {
    let mut machine_st = MachineState::new();
    let code_a = vec![
	Instruction::GetConstant(Level::Shallow, atom_as_cell!(atom!("a"), 0), RegType::Temp(1)),
	Instruction::Proceed
    ];
    let code_b = vec![
	Instruction::GetConstant(Level::Shallow, atom_as_cell!(atom!("b"), 0), RegType::Temp(1)),
	Instruction::Proceed
    ];
    let code_c = vec![
	Instruction::Allocate(1),
	Instruction::GetVariable(RegType::Perm(1), 2),
	Instruction::CallNamed(1, atom!("a"), CodeIndex::default(&mut machine_st.arena)),
	Instruction::PutValue(RegType::Perm(1), 1),
	Instruction::Deallocate,
	Instruction::ExecuteNamed(1, atom!("b"), CodeIndex::default(&mut machine_st.arena)),
    ];
    let x = heap_loc_as_cell!(0);
    let y = heap_loc_as_cell!(1);
    machine_st.registers[1] = x;
    machine_st.registers[2] = y;
    machine_st.heap.push(x);
    machine_st.heap.push(y);
    let mut jit = JitMachine::new();
    jit.compile("a", 1, code_a).unwrap();
    jit.compile("b", 1, code_b).unwrap();
    jit.compile("c", 2, code_c).unwrap();
    jit.exec("c", 2, &mut machine_st).unwrap();
    let mut machine_st_expected = MachineState::new();
    machine_st_expected.heap.push(atom_as_cell!(atom!("a"), 0));
    machine_st_expected.heap.push(atom_as_cell!(atom!("b"), 0));    
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.fail, false);
    
    
}
// TODO: Continue with more tests
