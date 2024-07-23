// This is another implementation of the JIT compiler
// In this implementation we do not share data between the interpreter and the compiled code
// We do copies before and after the execution

use crate::instructions::*;
use crate::machine::*;
use crate::parser::ast::*;

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
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
    heap_as_ptr: *const u8,
    heap_as_ptr_sig: Signature,
    heap_push: *const u8,
    heap_push_sig: Signature,
    heap_len: *const u8,
    heap_len_sig: Signature,
    predicates: HashMap<(String, usize), *const u8>,
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
	    ("enable_llvm_abi_extensions", "1")],
					     cranelift_module::default_libcall_names()
	).unwrap();
	builder.symbol("print_func", print_syscall as *const u8);
	let mut module = JITModule::new(builder);
	let pointer_type = module.isa().pointer_type();
	let call_conv = module.isa().default_call_conv();

	let mut ctx = module.make_context();
	let mut func_ctx = FunctionBuilderContext::new();
	
	let mut sig = module.make_signature();
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
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
	    let mut jump_sig = module.make_signature();
	    jump_sig.call_conv = isa::CallConv::Tail;
	    jump_sig.params.push(AbiParam::new(types::I64));
	    let mut params = vec![];
	    params.push(heap);	    
	    for i in 1..n+1 {
		jump_sig.params.push(AbiParam::new(types::I64));
		jump_sig.returns.push(AbiParam::new(types::I64));
		let reg_value = fn_builder.ins().load(types::I64, MemFlags::trusted(), registers, Offset32::new((i as i32)*8));
		params.push(reg_value);
	    }
	    let jump_sig_ref = fn_builder.import_signature(jump_sig);
	    let jump_call = fn_builder.ins().call_indirect(jump_sig_ref, func_addr, &params);
	    for i in 0..n {
		let reg_value = fn_builder.inst_results(jump_call)[i];
		fn_builder.ins().store(MemFlags::trusted(), reg_value, registers, Offset32::new(((i as i32) + 1) * 8));
	    }
	    fn_builder.ins().return_(&[]);
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
	let heap_as_ptr = Vec::<HeapCellValue>::as_ptr as *const u8;
	let mut heap_as_ptr_sig = module.make_signature();
	heap_as_ptr_sig.params.push(AbiParam::new(pointer_type));
	heap_as_ptr_sig.returns.push(AbiParam::new(pointer_type));
	let heap_push = Vec::<HeapCellValue>::push as *const u8;
	let mut heap_push_sig = module.make_signature();
	heap_push_sig.params.push(AbiParam::new(pointer_type));
	heap_push_sig.params.push(AbiParam::new(types::I64));
	let heap_len = Vec::<HeapCellValue>::len as *const u8;
	let mut heap_len_sig = module.make_signature();
	heap_len_sig.params.push(AbiParam::new(pointer_type));
	heap_len_sig.returns.push(AbiParam::new(types::I64));

	let predicates = HashMap::new();
	JitMachine {
	    trampolines,
	    module,
	    ctx,
	    func_ctx,
	    heap_as_ptr,
	    heap_as_ptr_sig,
	    heap_push,
	    heap_push_sig,
	    heap_len,
	    heap_len_sig,
	    predicates
	}
    }

    pub fn compile(&mut self, name: &str, arity: usize, code: Code) -> Result<(), JitCompileError> {
	let mut print_func_sig = self.module.make_signature();
        print_func_sig.params.push(AbiParam::new(types::I64));
        let print_func = self.module
            .declare_function("print_func", Linkage::Import, &print_func_sig)
            .unwrap();
	
	let mut sig = self.module.make_signature();
	sig.params.push(AbiParam::new(types::I64));
	for _ in 1..=arity {
	    sig.params.push(AbiParam::new(types::I64));
	    sig.returns.push(AbiParam::new(types::I64));
	}
	sig.call_conv = isa::CallConv::Tail;
	self.ctx.func.signature = sig.clone();
	self.ctx.set_disasm(true);

	let mut fn_builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);
	let block = fn_builder.create_block();
	fn_builder.append_block_params_for_function_params(block);
	fn_builder.switch_to_block(block);
	fn_builder.seal_block(block);

	let heap = fn_builder.block_params(block)[0];
	let mode = Variable::new(0);
	fn_builder.declare_var(mode, types::I8);
	let s = Variable::new(1);
	fn_builder.declare_var(s, types::I64);
	let fail = Variable::new(2);
	fn_builder.declare_var(fail, types::I8);
	let fail_value_init = fn_builder.ins().iconst(types::I8, 0);
	fn_builder.def_var(fail, fail_value_init);
	
	let mut registers = vec![];
	// TODO: This could be optimized more, we know the maximum register we're using
	for i in 1..MAX_ARITY {
	    if i <= arity {
	        let reg = fn_builder.block_params(block)[i];
	        registers.push(reg);
	    } else {
		let reg = fn_builder.ins().iconst(types::I64, 0);
		registers.push(reg);
	    }
	}

	macro_rules! print_rt {
	    ($x:expr) => {
		{
		    let print_func_fn = self.module.declare_func_in_func(print_func, &mut fn_builder.func);
		    fn_builder.ins().call(print_func_fn, &[$x]);
		}
	    }
	}

        macro_rules! heap_len {
	    () => {
		{let sig_ref = fn_builder.import_signature(self.heap_len_sig.clone());
		let heap_len_fn = fn_builder.ins().iconst(types::I64, self.heap_len as i64);
		let call_heap_len = fn_builder.ins().call_indirect(sig_ref, heap_len_fn, &[heap]);
		let heap_len = fn_builder.inst_results(call_heap_len)[0];
		 heap_len}
	    }
	}

	macro_rules! heap_as_ptr {
	    () => {
		{
		    let sig_ref = fn_builder.import_signature(self.heap_as_ptr_sig.clone());
		    let heap_as_ptr_fn = fn_builder.ins().iconst(types::I64, self.heap_as_ptr as i64);
		    let call_heap_as_ptr = fn_builder.ins().call_indirect(sig_ref, heap_as_ptr_fn, &[heap]);
		    let heap_ptr = fn_builder.inst_results(call_heap_as_ptr)[0];
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
		    let heap_ptr = heap_as_ptr!();
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
		    let heap_ptr = heap_as_ptr!();		    
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
		    print_rt!($x);
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    print_rt!(tag);
		    dbg!(HeapCellValueTag::Var as i64);
		    fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Var as i64)
		}
	    }
	}

	macro_rules! is_str {
	    ($x:expr) => {
		{
		    print_rt!($x);
		    let tag = fn_builder.ins().ushr_imm($x, 58);
		    print_rt!(tag);
		    dbg!(HeapCellValueTag::Str as i64);
		    fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Str as i64)
		}
	    }
	}	

	// TODO: Unify
	macro_rules! unify {
	    ($x:expr, $y:expr) => {
		{
    		    let loop_block = fn_builder.create_block();
		    fn_builder.append_block_param(loop_block, types::I64);
		    let continue_loop_block = fn_builder.create_block();
		    let check_var_block = fn_builder.create_block();
		    let is_var_block = fn_builder.create_block();
		    let is_str_block = fn_builder.create_block();
		    let push_str_block = fn_builder.create_block();
		    let push_str_loop_block = fn_builder.create_block();
		    let push_str_loop_check_block = fn_builder.create_block();
		    let exit_failure = fn_builder.create_block();
		    let exit = fn_builder.create_block();
		    let pdl = fn_builder.create_dynamic_stack_slot(DynamicStackSlotData::new(StackSlotKind::ExplicitDynamicSlot, DynamicType::from_u32(64)));
		    let pdl_size = fn_builder.ins().iconst(types::I64, 2);
		    fn_builder.ins().dynamic_stack_store($x, pdl);
		    fn_builder.ins().dynamic_stack_store($y, pdl);
		    fn_builder.ins().jump(loop_block, &[pdl_size]);
		    // loop_block
		    fn_builder.switch_to_block(loop_block);
		    let pdl_size = fn_builder.block_params(loop_block)[0];
		    fn_builder.ins().brif(pdl_size, continue_loop_block, &[], exit, &[]);
		    fn_builder.seal_block(continue_loop_block);
		    fn_builder.seal_block(exit);
		    // continue_loop_block
		    fn_builder.switch_to_block(continue_loop_block);
		    let d1 = fn_builder.ins().dynamic_stack_load(types::I64, pdl);
		    let d1 = deref!(d1);
		    let d2 = fn_builder.ins().dynamic_stack_load(types::I64, pdl);
		    let d2 = deref!(d2);
		    let pdl_size = fn_builder.ins().iadd_imm(pdl_size, -2);
		    let are_equal = fn_builder.ins().icmp(IntCC::Equal, d1, d2);
		    fn_builder.ins().brif(are_equal, loop_block, &[pdl_size], check_var_block, &[]);
		    fn_builder.seal_block(check_var_block);
		    // check_var_block
		    fn_builder.switch_to_block(check_var_block);
		    let d1 = store!(d1);
		    let d2 = store!(d2);
		    let tag_d1 = fn_builder.ins().ushr_imm(d1, 58);
		    let is_var_d1 = fn_builder.ins().icmp_imm(IntCC::Equal, tag_d1, HeapCellValueTag::Var as i64);
		    let tag_d2 = fn_builder.ins().ushr_imm(d2, 58);
		    let is_var_d2 = fn_builder.ins().icmp_imm(IntCC::Equal, tag_d2, HeapCellValueTag::Var as i64);
		    let any_var = fn_builder.ins().bor(is_var_d1, is_var_d2);
		    fn_builder.ins().brif(any_var, is_var_block, &[], is_str_block, &[]);
		    fn_builder.seal_block(is_var_block);
		    fn_builder.seal_block(is_str_block);

		    // is_var_block
		    fn_builder.switch_to_block(is_var_block);
		    bind!(d1, d2);
		    fn_builder.ins().jump(loop_block, &[pdl_size]);

		    // is_str_block
		    fn_builder.switch_to_block(is_str_block);
		    let heap_ptr = heap_as_ptr!();
		    let idx = fn_builder.ins().ishl_imm(d1, 8);
		    let idx = fn_builder.ins().ushr_imm(idx, 5);
		    let idx1 = fn_builder.ins().iadd(heap_ptr, idx);
		    let heap_d1 = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx1, Offset32::new(0));
		    let idx = fn_builder.ins().ishl_imm(d2, 8);
		    let idx = fn_builder.ins().ushr_imm(idx, 5);
		    let idx2 = fn_builder.ins().iadd(heap_ptr, idx);
		    let heap_d2 = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx2, Offset32::new(0));
		    let is_str_equal = fn_builder.ins().icmp(IntCC::Equal, heap_d1, heap_d2);
		    fn_builder.ins().brif(is_str_equal, push_str_block, &[], exit_failure, &[]);
		    fn_builder.seal_block(push_str_block);
		    fn_builder.seal_block(exit_failure);

		    // push_str_block
		    fn_builder.switch_to_block(push_str_block);
		    let arity = fn_builder.ins().ishl_imm(heap_d1, 8);
		    let arity = fn_builder.ins().ushr_imm(arity, 54);
		    let n = fn_builder.ins().iconst(types::I64, 8);
		    fn_builder.ins().jump(push_str_loop_check_block, &[pdl_size, n]);
		    fn_builder.seal_block(push_str_loop_check_block);		    
		    // push_str_loop_check_block
		    fn_builder.switch_to_block(push_str_loop_check_block);
		    let pdl_size = fn_builder.block_params(push_str_loop_check_block)[0];		    
		    let n = fn_builder.block_params(push_str_loop_check_block)[1];
		    let n_is_arity = fn_builder.ins().icmp(IntCC::Equal, arity, n);
		    fn_builder.ins().brif(n_is_arity, loop_block, &[], push_str_loop_block, &[pdl_size, n]);
		    fn_builder.seal_block(loop_block);

		    // push_str_loop_block
		    fn_builder.switch_to_block(push_str_loop_block);
		    let n = fn_builder.block_params(push_str_loop_block)[0];
		    let v1 = fn_builder.ins().iadd(idx1, n);
		    let v2 = fn_builder.ins().iadd(idx2, n);
		    let heap_v1 = fn_builder.ins().load(types::I64, MemFlags::trusted(), v1, Offset32::new(0));
		    let heap_v2 = fn_builder.ins().load(types::I64, MemFlags::trusted(), v2, Offset32::new(0));
		    fn_builder.ins().dynamic_stack_store(heap_v1, pdl);
		    fn_builder.ins().dynamic_stack_store(heap_v2, pdl);
		    let pdl_size = fn_builder.ins().iadd_imm(pdl_size, 2);
		    let n = fn_builder.ins().iadd_imm(n, 8);
		    fn_builder.ins().jump(push_str_loop_block, &[pdl_size, n]);
		    fn_builder.seal_block(push_str_loop_check_block);
		    
		    // exit_failure
		    fn_builder.switch_to_block(exit_failure);
	            let fail_value = fn_builder.ins().iconst(types::I8, 1);
		    fn_builder.def_var(fail, fail_value);
		    fn_builder.ins().jump(exit, &[]);

		    // exit
		    fn_builder.switch_to_block(exit);
		}
	    }
	}
	
	for wam_instr in code {
	    match wam_instr {
		// TODO Missing RegType Perm
		/* put_structure is an instruction that puts a new STR in the heap
		 * (STR cell, plus functor + arity cell)
		 * It also saves the STR cell into a register
		 */
		Instruction::PutStructure(name, arity, reg) => {
		    let atom_cell = atom_as_cell!(name, arity);
		    let atom = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(atom_cell.into_bytes()));
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, atom]);
		    let str_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(str_loc_as_cell!(0).into_bytes()));
		    let heap_len = heap_len!();
		    let str_loc = fn_builder.ins().iadd_imm(heap_len, -1);
		    let str_cell = fn_builder.ins().bor(str_loc, str_cell);
		    match reg {
			RegType::Temp(x) => {
			    registers[x-1] = str_cell;
			}
			_ => unimplemented!()
		    }
		}
		// TODO Missing RegType Perm
		/* set_variable is an instruction that creates a new self-referential REF
		 * (unbounded variable) in the heap and saves that into a register
		 */
		Instruction::SetVariable(reg) => {
		    let heap_loc_cell = heap_loc_as_cell!(0);
		    let heap_loc_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(heap_loc_cell.into_bytes()));
		    let heap_len = heap_len!();
		    let heap_loc_cell = fn_builder.ins().bor(heap_len, heap_loc_cell);
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, heap_loc_cell]);
		    match reg {
			RegType::Temp(x) => {
			    registers[x-1] = heap_loc_cell;
			}
			_ => unimplemented!()
		    }
		}
		// TODO: Missing RegType Perm
		/* set_value is an instruction that pushes a new data cell from a register to the heap
		 */
		Instruction::SetValue(reg) => {
		    let value = match reg {
			RegType::Temp(x) => {
			    registers[x-1]
			},
			_ => unimplemented!()
		    };
		    let value = store!(value);
		    
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, value]);
		}
		// TODO: Missing RegType Perm
		/* get_structure is an instruction that either matches an existing STR or starts writing a new
		 * STR into the heap. If the cell passed via register is an unbounded REF, we start WRITE mode
		 * and unify_variable, unify_value behave similar to set_variable, set_value.
		 * If it's an existing STR, we check functor and arity, set S pointer and start READ mode,
		 * in that mod unify_variable and unify_value will follow the unification procedure
		 */
		Instruction::GetStructure(_lvl, name, arity, reg) => {
		    let xi = match reg {
			RegType::Temp(x) => {
			    registers[x-1]
			}
			_ => unimplemented!()
		    };
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
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);		    
		    let str_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(str_loc_as_cell!(0).into_bytes()));
		    let heap_len = heap_len!();
		    let str_cell = fn_builder.ins().bor(heap_len, str_cell);
		    let atom_cell = atom_as_cell!(name, arity);
		    let atom = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(atom_cell.into_bytes()));
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, atom]);
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
    		    let heap_ptr = heap_as_ptr!();
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
		    let s_ptr = fn_builder.ins().iadd_imm(heap_ptr, 8);
		    fn_builder.def_var(s, s_ptr);
		    let mode_value = fn_builder.ins().iconst(types::I8, 0);
		    fn_builder.def_var(mode, mode_value);
		    fn_builder.ins().jump(exit_block, &[]);

		    // fail_block
		    fn_builder.switch_to_block(fail_block);
		    let fail_value = fn_builder.ins().iconst(types::I8, 1);
		    fn_builder.def_var(fail, fail_value);
		    fn_builder.ins().jump(exit_block, &[]);

		    // exit_block
		    fn_builder.seal_block(exit_block);
		    fn_builder.switch_to_block(exit_block);
		    
		}
		// TODO: Missing RegType Perm. Let's suppose Mode is local to each predicate
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
		    let heap_ptr = heap_as_ptr!();
		    let s_value = fn_builder.use_var(s);
		    let idx = fn_builder.ins().iadd(heap_ptr, s_value);
		    let value = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx, Offset32::new(0));
		    let value = deref!(value);
		    match reg {
			RegType::Temp(x) => {
			    registers[x-1] = value;
			},
			_ => unimplemented!()
		    }
		    let sum_s = fn_builder.ins().iadd_imm(s_value, 8);
		    fn_builder.def_var(s, sum_s);
		    fn_builder.ins().jump(exit_block, &[]);
		    // write (equal to SetVariable)
		    fn_builder.switch_to_block(write_block);
		    let heap_loc_cell = heap_loc_as_cell!(0);
		    let heap_loc_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(heap_loc_cell.into_bytes()));
		    let heap_len = heap_len!();
		    let heap_len_shift = fn_builder.ins().ishl_imm(heap_len, 8);
		    let heap_loc_cell = fn_builder.ins().bor(heap_len_shift, heap_loc_cell);
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, heap_loc_cell]);
		    match reg {
			RegType::Temp(x) => {
			    registers[x-1] = heap_loc_cell;
			}
			_ => unimplemented!()
		    }
		    fn_builder.ins().jump(exit_block, &[]);
		    // exit
		    fn_builder.switch_to_block(exit_block);
		    fn_builder.seal_block(exit_block);
		    
		}
		/* unify_value is an instruction that on WRITE mode behaves like set_value, and in READ mode
		 * executes unification
		 */
		// TODO: Manage RegType Perm
		Instruction::UnifyValue(reg) => {
		    let reg = match reg {
			RegType::Temp(x) => {
			    registers[x-1]
			}
			_ => unimplemented!()
		    };
    		    let read_block = fn_builder.create_block();
		    let write_block = fn_builder.create_block();
		    let exit_block = fn_builder.create_block();
		    let mode_value = fn_builder.use_var(mode);
		    fn_builder.ins().brif(mode_value, write_block, &[], read_block, &[]);
		    fn_builder.seal_block(read_block);
		    fn_builder.seal_block(write_block);
		    // read
		    fn_builder.switch_to_block(read_block);
		    let heap_ptr = heap_as_ptr!();
		    let s_value = fn_builder.use_var(s);
		    let idx = fn_builder.ins().iadd(heap_ptr, s_value);
		    let value = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx, Offset32::new(0));
		    unify!(reg, value);
		    let s_value  = fn_builder.ins().iadd_imm(s_value, 8);
		    fn_builder.def_var(s, s_value);
		    fn_builder.ins().jump(exit_block, &[]);
		    // write
		    fn_builder.switch_to_block(write_block);
    		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, value]);
		    fn_builder.ins().jump(exit_block, &[]);
		    fn_builder.seal_block(exit_block);

		    // exit
		    fn_builder.switch_to_block(exit_block);
		    
		}
		// TODO: Manage RegType Perm
		// TODO: manage NonVar cases
		// TODO: Manage unification case
		// TODO: manage STORE[addr] is not REF
		Instruction::GetConstant(_, c, reg) => {
		    let value = match reg {
			RegType::Temp(x) => {
			    registers[x-1]
			}
			_ => unimplemented!()
		    };
		    let value = deref!(value);
		    let value = store!(value);
		    // The order of HeapCellValue is TAG (6), M (1), F (1), VALUE (56)
		    let c = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(c.into_bytes()));
		    bind!(value, c);
		}
		Instruction::Proceed => {
		    fn_builder.ins().return_(&registers[0..arity]);
		    break;
	        },
	        _ => {
		    fn_builder.finalize();
	            self.module.clear_context(&mut self.ctx);	
		    return Err(JitCompileError::InstructionNotImplemented);
	        }
	    }
	}
	fn_builder.seal_all_blocks();
	fn_builder.finalize();

	let func = self.module.declare_function(name, Linkage::Local, &sig).unwrap();
	self.module.define_function(func, &mut self.ctx).unwrap();
	println!("{}", self.ctx.func.display());
	self.module.finalize_definitions().unwrap();	
	let code_ptr = self.module.get_finalized_function(func);
	self.predicates.insert((name.to_string(), arity), code_ptr);
	println!("{}", self.ctx.compiled_code().unwrap().vcode.clone().unwrap());
	self.module.clear_context(&mut self.ctx);
	Ok(())
    }

    pub fn exec(&self, name: &str, arity: usize, machine_st: &mut MachineState) -> Result<(), ()> {
	let Some(predicate) = self.predicates.get(&(name.to_string(), arity)) else {
	    return Err(());
	};
	let trampoline: extern "C" fn (*const u8, *mut Registers, *const Vec<HeapCellValue>) = unsafe { std::mem::transmute(self.trampolines[arity])};
	let registers = machine_st.registers.as_ptr() as *mut Registers;
	let heap = &machine_st.heap as *const Vec<HeapCellValue>;
	trampoline(*predicate, registers, heap);
	machine_st.p = machine_st.cp;
	Ok(())
    }
}


fn print_syscall(value: i64) {
    println!("{}", value);
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
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 2));
    machine_st_expected.registers[1] = str_loc_as_cell!(0);
    assert_eq!(machine_st.heap, machine_st_expected.heap);
    assert_eq!(machine_st.registers, machine_st_expected.registers);
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
    assert_eq!(machine_st.registers, machine_st_expected.registers);
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
    machine_st_expected.heap.push(atom_as_cell!(atom!("h"), 2));
    machine_st_expected.heap.push(heap_loc_as_cell!(1));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(2));
    machine_st_expected.heap.push(atom_as_cell!(atom!("p"), 3));
    machine_st_expected.heap.push(heap_loc_as_cell!(1));
    machine_st_expected.heap.push(str_loc_as_cell!(0));
    machine_st_expected.heap.push(str_loc_as_cell!(3));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
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
    machine_st_expected.heap.push(atom_as_cell!(atom!("f"), 1));
    machine_st_expected.heap.push(heap_loc_as_cell!(1));
    assert_eq!(machine_st.heap, machine_st_expected.heap);
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
}

// TODO: Continue with more tests
