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


	JitMachine {
	    trampolines,
	    module,
	    ctx,
	    func_ctx,
	}
    }

    // TODO: Compile taking into account arity
    pub fn compile(&mut self, name: &str, code: Code) -> Result<(), JitCompileError> {
	let mut fn_builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.func_ctx);
	let block = fn_builder.create_block();
	fn_builder.append_block_params_for_function_params(block);
	fn_builder.switch_to_block(block);

	for wam_instr in code {
	    match wam_instr {
		Instruction::Proceed => {
		    fn_builder.ins().return_(&[]);
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

	let mut sig = self.module.make_signature();
	sig.call_conv = isa::CallConv::Tail;

	let func = self.module.declare_function(name, Linkage::Local, &sig).unwrap();
	self.module.define_function(func, &mut self.ctx).unwrap();
	println!("{}", self.ctx.func.display());
	self.module.clear_context(&mut self.ctx);
	Ok(())
    }

    pub fn exec(&self, name: &str, machine_st: &mut MachineState) -> Result<(), ()> {
	Ok(())
    }
}
