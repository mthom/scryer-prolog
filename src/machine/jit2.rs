// This is another implementation of the JIT compiler
// In this implementation we do not share data between the interpreter and the compiled code
// We do copies before and after the execution

use crate::instructions::*;
use crate::machine::*;
use crate::parser::ast::*;

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use cranelift_codegen::Context;
use cranelift::prelude::codegen::ir::immediates::Offset32;
use cranelift::prelude::codegen::ir::entities::Value;

use std::ops::Index;

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
}

impl std::fmt::Debug for JitMachine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "JitMachine")
    }
}


impl JitMachine {
    pub fn new() -> Self {
	let builder = JITBuilder::with_flags(&[
	    ("preserve_frame_pointers", "true"),
	    ("enable_llvm_abi_extensions", "1")],
					     cranelift_module::default_libcall_names()
	).unwrap();
	let mut module = JITModule::new(builder);
	let pointer_type = module.isa().pointer_type();
	let call_conv = module.isa().default_call_conv();

	let mut ctx = module.make_context();
	let mut func_ctx = FunctionBuilderContext::new();
	
	let mut sig = module.make_signature();
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
	    let mut jump_sig = module.make_signature();
	    jump_sig.call_conv = isa::CallConv::Tail;
	    let mut params = vec![];
	    for i in 1..n+1 {
		jump_sig.params.push(AbiParam::new(types::I64));
		let reg_value = fn_builder.ins().load(types::I64, MemFlags::new(), registers, Offset32::new((i as i32)*8));
		params.push(reg_value);
	    }
	    let jump_sig_ref = fn_builder.import_signature(jump_sig);
	    fn_builder.ins().call_indirect(jump_sig_ref, func_addr, &params);
	    fn_builder.ins().return_(&[]);
	    fn_builder.seal_block(block);
	    fn_builder.finalize();

	    let func = module.declare_function(&format!("$trampoline/{}", n), Linkage::Local, &sig).unwrap();
	    module.define_function(func, &mut ctx).unwrap();
	    println!("{}", ctx.func.display());
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
	}
    }

    pub fn compile(&mut self, name: &str, arity: usize, code: Code) -> Result<(), JitCompileError> {
	let mut sig = self.module.make_signature();
	sig.params.push(AbiParam::new(types::I64));
	for _ in 1..=arity {
	    sig.params.push(AbiParam::new(types::I64));
	    sig.returns.push(AbiParam::new(types::I64));
	}
	sig.call_conv = isa::CallConv::Tail;
	self.ctx.func.signature = sig.clone();

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
	
	let mut registers = vec![];
	for i in 1..=arity {
	    let reg = fn_builder.block_params(block)[i];
	    registers.push(reg);
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

	macro_rules! store {
	    ($x:expr) => {
		{
		    let merge_block = fn_builder.create_block();
		    fn_builder.append_block_param(merge_block, types::I64);
		    let is_var_block = fn_builder.create_block();
		    fn_builder.append_block_param(is_var_block, types::I64);
		    let is_not_var_block = fn_builder.create_block();
		    fn_builder.append_block_param(is_not_var_block, types::I64);
		    let tag = fn_builder.ins().band_imm($x, 64);
		    let is_var = fn_builder.ins().icmp_imm(IntCC::Equal, tag, HeapCellValueTag::Var as i64);
		    fn_builder.ins().brif(is_var, is_var_block, &[$x], is_not_var_block, &[$x]);
		    // is_var
		    fn_builder.switch_to_block(is_var_block);
		    fn_builder.seal_block(is_var_block);
		    let param = fn_builder.block_params(is_var_block)[0];
		    let idx = fn_builder.ins().ushr_imm(param, 8);
		    let heap_ptr = heap_as_ptr!();
		    let idx_ptr = fn_builder.ins().imul_imm(idx, 8);
		    let idx_ptr = fn_builder.ins().iadd(heap_ptr, idx_ptr);
		    let heap_value = fn_builder.ins().load(types::I64, MemFlags::trusted(), idx_ptr, Offset32::new(0));
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
		    let tag = fn_builder.ins().band_imm(value, 64);
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

	for wam_instr in code {
	    match wam_instr {
		// TODO Missing RegType Perm
		Instruction::PutStructure(name, arity, reg) => {
		    let atom_cell = atom_as_cell!(name, arity);
		    let atom = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(atom_cell.into_bytes()));
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, atom]);
		    let str_cell = fn_builder.ins().iconst(types::I64, i64::from_le_bytes(str_loc_as_cell!(0).into_bytes()));
		    let heap_len = heap_len!();
		    let heap_len_shift = fn_builder.ins().ishl_imm(heap_len, 8);
		    let str_cell = fn_builder.ins().bor(heap_len_shift, str_cell);
		    match reg {
			RegType::Temp(x) => {
			    registers[x] = str_cell;
			}
			_ => unimplemented!()
		    }
		}
		// TODO Missing RegType Perm
		Instruction::SetVariable(reg) => {
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
			    registers[x] = heap_loc_cell;
			}
			_ => unimplemented!()
		    }
		}
		// TODO: Missing RegType Perm
		Instruction::SetValue(reg) => {
		    let value = match reg {
			RegType::Temp(x) => {
			    registers[x]
			},
			_ => unimplemented!()
		    };
		    let value = store!(value);
		    
		    let sig_ref = fn_builder.import_signature(self.heap_push_sig.clone());
		    let heap_push_fn = fn_builder.ins().iconst(types::I64, self.heap_push as i64);
		    fn_builder.ins().call_indirect(sig_ref, heap_push_fn, &[heap, value]);
		}
		// TODO: Missing RegType Perm. Let's suppose Mode is local to each predicate
		// TODO: Missing support for PStr and CStr
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
			    registers[x] = value;
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
			    registers[x] = heap_loc_cell;
			}
			_ => unimplemented!()
		    }
		    fn_builder.ins().jump(exit_block, &[]);
		    // exit
		    fn_builder.switch_to_block(exit_block);
		    fn_builder.seal_block(exit_block);
		    
		}
		Instruction::Proceed => {
		    fn_builder.ins().return_(&registers);
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
	self.module.clear_context(&mut self.ctx);
	Ok(())
    }

    pub fn exec(&self, name: &str, machine_st: &mut MachineState) -> Result<(), ()> {
	Err(())
    }
}
