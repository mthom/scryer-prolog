use std::collections::HashMap;

use crate::instructions::*;
use crate::machine::*;
use crate::machine::arithmetic_ops::add_jit;

use cranelift::prelude::*;
use cranelift::prelude::codegen::ir::immediates::Offset32;
use cranelift::prelude::codegen::ir::entities::Value;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};

struct CompileOutput {
    module: JITModule,
    code_ptr: *const u8,
}

#[derive(Debug, PartialEq)]
pub enum JitCompileError {
    UndefinedPredicate,
    InstructionNotImplemented,
}

pub struct JitMachine {
    modules: HashMap<String, CompileOutput>,
    trampoline: extern "C" fn (*mut MachineState, *mut Registers, *const u8),
    offset_interms: usize,
    offset_arena: usize,
    offset_heap: usize,
    write_literal_to_var: *const u8,
    deref: *const u8,
    store: *const u8,
    unify_num: *const u8,
    get_number: *const u8,
    add: *const u8,
    vec_as_ptr: *const u8,
    vec_push: *const u8,
    number_try_from: *const u8,
}

impl std::fmt::Debug for JitMachine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "JitMachine")
    }
}

impl JitMachine {
    pub fn new() -> Self {
	// Build trampoline: from SysV to Tail
        let mut builder = JITBuilder::with_flags(&[("preserve_frame_pointers", "true"), ("enable_llvm_abi_extensions", "1")], cranelift_module::default_libcall_names()).unwrap();
	
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
	ctx.func.signature = sig.clone();

	let mut func = module.declare_function("$trampoline", Linkage::Local, &sig).unwrap();
	let mut fn_builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
	let block = fn_builder.create_block();
	fn_builder.append_block_params_for_function_params(block);
	fn_builder.switch_to_block(block);
	let machine_state = fn_builder.block_params(block)[0];
	let machine_registers = fn_builder.block_params(block)[1];
	let func_addr = fn_builder.block_params(block)[2];

	let mut sig = module.make_signature();
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.call_conv = isa::CallConv::Tail;
	let sig_ref = fn_builder.import_signature(sig);
	fn_builder.ins().call_indirect(sig_ref, func_addr, &[machine_state, machine_registers]);
	fn_builder.ins().return_(&[]);
	fn_builder.seal_all_blocks();
	fn_builder.finalize();
	
        module.define_function(func, &mut ctx).unwrap();
	module.clear_context(&mut ctx);

	module.finalize_definitions().unwrap();

	let code_ptr = unsafe { std::mem::transmute(module.get_finalized_function(func)) };

	let machine_st = std::mem::MaybeUninit::uninit();
	let machine_st_ptr: *const MachineState = machine_st.as_ptr();
        let machine_st_ptr_u8 = machine_st_ptr as *const u8;	
	let offset_interms = unsafe {
	    let interms_ptr = std::ptr::addr_of!((*machine_st_ptr).interms) as *const u8;
	    interms_ptr.offset_from(machine_st_ptr_u8) as usize
	};
	let offset_arena = unsafe {
	    let arena_ptr = std::ptr::addr_of!((*machine_st_ptr).arena) as *const u8;
	    arena_ptr.offset_from(machine_st_ptr_u8) as usize
	};
	let offset_heap = unsafe {
	    let heap_ptr = std::ptr::addr_of!((*machine_st_ptr).heap) as *const u8;
	    heap_ptr.offset_from(machine_st_ptr_u8) as usize
	};
	JitMachine {
	    modules: HashMap::new(),
	    trampoline: code_ptr,
	    offset_interms: offset_interms,
	    offset_arena: offset_arena,
	    offset_heap: offset_heap,
	    write_literal_to_var: MachineState::write_literal_to_var as *const u8,
	    deref: MachineState::deref as *const u8,
	    store: MachineState::store as *const u8,
	    unify_num: MachineState::unify_num_jit as *const u8,
	    get_number: MachineState::get_number as *const u8,
	    add: add_jit as *const u8,
	    vec_as_ptr: Vec::<Number>::as_ptr as *const u8,
	    vec_push: Vec::<HeapCellValue>::push as *const u8,
	    number_try_from: Number::jit_try_from as *const u8,
	}
    }

    // For now, one module = one predicate
    // Access to MachineState via global pointer
    // MachineState Registers + ShadowRegisters??
    // Use TAIL call convention
    pub fn compile(&mut self, name: &str, code: Code) -> Result<(), JitCompileError>{
        let mut builder = JITBuilder::with_flags(&[("preserve_frame_pointers", "true"), ("enable_llvm_abi_extensions", "1")], cranelift_module::default_libcall_names()).unwrap();
	builder.symbols(self.modules.iter().map(|(k, v)| (k,v.code_ptr)));
	
	let mut module = JITModule::new(builder);
	let pointer_type = module.isa().pointer_type();
	let call_conv = module.isa().default_call_conv();
	let mut ctx = module.make_context();
	let mut func_ctx = FunctionBuilderContext::new();

	let mut sig = module.make_signature();
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(pointer_type));
	sig.call_conv = isa::CallConv::Tail;
	ctx.func.signature = sig.clone();

	let mut func = module.declare_function(name, Linkage::Local, &sig).unwrap();

	let mut fn_builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);
	let block = fn_builder.create_block();
 	fn_builder.append_block_params_for_function_params(block);
	fn_builder.switch_to_block(block);
	// TODO: Manage failure
	for wam_instr in code {
	    match wam_instr {
		Instruction::Proceed => {
		    fn_builder.ins().return_(&[]);
		    fn_builder.seal_all_blocks();
		    fn_builder.finalize();
		    break;
		}
		Instruction::ExecuteNamed(arity, pred_name, ..) => {
    		    let machine_state_value = fn_builder.block_params(block)[0];
		    let reg_ptr = fn_builder.block_params(block)[1];		    
		    let mut callee_func_sig = module.make_signature();
		    callee_func_sig.call_conv = isa::CallConv::Tail;
		    callee_func_sig.params.push(AbiParam::new(pointer_type));
		    callee_func_sig.params.push(AbiParam::new(pointer_type));
		    if let Ok(callee_func) = module.declare_function(&format!("{}/{}", pred_name.as_str(), arity), Linkage::Import, &callee_func_sig) {
			let func_ref = module.declare_func_in_func(callee_func, fn_builder.func);
			fn_builder.ins().return_call(func_ref, &[machine_state_value, reg_ptr]);
			fn_builder.seal_all_blocks();
			fn_builder.finalize();
			break;
		    } else {
			return Err(JitCompileError::UndefinedPredicate);
		    }
		}
		// TODO Manage RegType
		Instruction::GetConstant(_, c, reg) => {
    		    let machine_state_value = fn_builder.block_params(block)[0];
		    let reg_ptr = fn_builder.block_params(block)[1];
		    let reg_num = reg.reg_num();
		    let reg_value = fn_builder.ins().load(types::I64, MemFlags::new(), reg_ptr, Offset32::new((reg_num as i32)*8));
		    let mut sig = module.make_signature();
		    sig.call_conv = call_conv;
		    sig.params.push(AbiParam::new(pointer_type));
		    sig.params.push(AbiParam::new(types::I64));
		    sig.returns.push(AbiParam::new(types::I64));
		    let sig_ref = fn_builder.import_signature(sig);
		    let deref = fn_builder.ins().iconst(types::I64, self.deref as i64);
		    let deref_call = fn_builder.ins().call_indirect(sig_ref, deref, &[machine_state_value, reg_value]);
		    let reg_value = fn_builder.inst_results(deref_call)[0];
		    let c = unsafe { std::mem::transmute::<u64, i64>(u64::from(c)) };		    
		    let c_value = fn_builder.ins().iconst(types::I64, c);
		    let mut sig = module.make_signature();
		    sig.call_conv = call_conv;
		    sig.params.push(AbiParam::new(types::I64));
		    sig.params.push(AbiParam::new(types::I64));
		    sig.params.push(AbiParam::new(types::I64));
		    let sig_ref = fn_builder.import_signature(sig);
		    let write_literal_to_var = fn_builder.ins().iconst(types::I64, self.write_literal_to_var as i64);
		    fn_builder.ins().call_indirect(sig_ref, write_literal_to_var, &[machine_state_value, reg_value, c_value]);
		}
		// TODO: Manage RegType
		Instruction::GetVariable(norm, arg) => {
		    let reg_ptr = fn_builder.block_params(block)[1];
		    let value = fn_builder.ins().load(types::I64, MemFlags::new(), reg_ptr, Offset32::new((arg as i32)*8));
		    match norm {
			RegType::Temp(temp) => {
			    fn_builder.ins().store(MemFlags::new(), value, reg_ptr, Offset32::new((temp as i32)*8));
			}
			_ => unimplemented!()
		    }
		}
		// TODO Manage RegType
		Instruction::PutConstant(_, c, reg) => {
		    let reg_ptr = fn_builder.block_params(block)[1];
		    let reg_num = reg.reg_num();
		    let c = unsafe { std::mem::transmute::<u64, i64>(u64::from(c)) };
		    let c_value = fn_builder.ins().iconst(types::I64, c);
		    fn_builder.ins().store(MemFlags::new(), c_value, reg_ptr, Offset32::new((reg_num as i32)*8));
		}
		Instruction::PutValue(norm, arg) => {
		    let reg_ptr = fn_builder.block_params(block)[1];
		    match norm {
			RegType::Temp(temp) => {
			    let value = fn_builder.ins().load(types::I64, MemFlags::new(), reg_ptr, Offset32::new((temp as i32)*8));
			    fn_builder.ins().store(MemFlags::new(), value, reg_ptr, Offset32::new((arg as i32)*8));
			}
			_ => unimplemented!()
		    }
		}
		Instruction::SetConstant(c) => {
		    let machine_st = fn_builder.block_params(block)[0];
		    let mut sig = module.make_signature();
		    sig.call_conv = call_conv;
		    sig.params.push(AbiParam::new(pointer_type));
		    let sig_ref = fn_builder.import_signature(sig);
		    let heap = fn_builder.ins().iadd_imm(machine_st, self.offset_heap as i64);
		    let vec_push = fn_builder.ins().iconst(types::I64, self.vec_push as i64);
		    let c = unsafe { std::mem::transmute::<u64, i64>(u64::from(c)) };
		    let c_value = fn_builder.ins().iconst(types::I64, c);
		    fn_builder.ins().call_indirect(sig_ref, vec_push, &[heap, c_value]);
		}
		// TODO Fill more cases. Can we optimize the add in some cases to use the Cranelift add?
		Instruction::Add(a1, a2, t) => {
		    let machine_state = fn_builder.block_params(block)[0];
		    let reg_ptr = fn_builder.block_params(block)[1];
		    let n1 = self.jit_get_number(&module, machine_state, reg_ptr, &mut fn_builder, a1);
		    let n2 = self.jit_get_number(&module, machine_state, reg_ptr, &mut fn_builder, a2);
		    let mut sig = module.make_signature();
		    sig.call_conv = call_conv;
		    sig.params.push(AbiParam::new(types::I128));
		    sig.params.push(AbiParam::new(types::I128));
		    sig.params.push(AbiParam::new(pointer_type));
		    sig.returns.push(AbiParam::new(types::I128));
		    let sig_ref = fn_builder.import_signature(sig);
		    let arena = fn_builder.ins().iadd_imm(machine_state, self.offset_arena as i64);
		    let add_jit = fn_builder.ins().iconst(types::I64, self.add as i64);
		    let add_jit_call = fn_builder.ins().call_indirect(sig_ref, add_jit, &[n1, n2, arena]);
		    let n3 = fn_builder.inst_results(add_jit_call)[0];

		    let interms_vec = fn_builder.ins().iadd_imm(machine_state, self.offset_interms as i64);
		    let mut sig = module.make_signature();
		    sig.call_conv = call_conv;
		    sig.params.push(AbiParam::new(pointer_type));
		    sig.returns.push(AbiParam::new(pointer_type));
		    let sig_ref = fn_builder.import_signature(sig);
		    let vec_ptr = fn_builder.ins().iconst(types::I64, self.vec_as_ptr as i64);
		    let vec_ptr_call = fn_builder.ins().call_indirect(sig_ref, vec_ptr, &[interms_vec]);
		    let interms = fn_builder.inst_results(vec_ptr_call)[0];
		    fn_builder.ins().store(MemFlags::new(), n3, interms, Offset32::new((t as i32 - 1) * 16));
		}
		Instruction::ExecuteIs(r, at) => {
		    let machine_state = fn_builder.block_params(block)[0];
		    let reg_ptr = fn_builder.block_params(block)[1];
		    let n1 = self.jit_store_deref_reg(&module, machine_state, reg_ptr, &mut fn_builder, r);
		    let n = self.jit_get_number(&module, machine_state, reg_ptr, &mut fn_builder, at);

		    let mut sig = module.make_signature();
		    sig.call_conv = call_conv;
		    sig.params.push(AbiParam::new(pointer_type));
		    sig.params.push(AbiParam::new(types::I128));
		    sig.params.push(AbiParam::new(types::I64));
		    let sig_ref = fn_builder.import_signature(sig);
		    let unify_num = fn_builder.ins().iconst(types::I64, self.unify_num as i64);
		    fn_builder.ins().call_indirect(sig_ref, unify_num, &[machine_state, n, n1]);
		    fn_builder.ins().return_(&[]);
		    fn_builder.seal_all_blocks();
		    fn_builder.finalize();
		    break;
		}
		_ => {
		    return Err(JitCompileError::InstructionNotImplemented);
		}
	    }
	}
	module.define_function(func, &mut ctx).unwrap();
	println!("{}", ctx.func.display());	
	module.clear_context(&mut ctx);

	module.finalize_definitions().unwrap();
	let code_ptr = unsafe { std::mem::transmute(module.get_finalized_function(func)) };
	self.modules.insert(name.to_string(), CompileOutput {
	    module,
	    code_ptr
	});
	Ok(())
    }
    
    fn jit_store_deref_reg(&self, module: &JITModule, machine_state: Value, reg_ptr: Value, fn_builder: &mut FunctionBuilder, reg: RegType) -> Value {
	let pointer_type = module.isa().pointer_type();
	let system_call_conv = module.isa().default_call_conv();
	let n1 = match reg {
	    RegType::Temp(temp) => {
		fn_builder.ins().load(types::I64, MemFlags::new(), reg_ptr, Offset32::new((temp as i32)*8))
	    }
	    _ => unimplemented!() // TODO
	};

	let mut sig = module.make_signature();
	sig.call_conv = system_call_conv;
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(types::I64));
	sig.returns.push(AbiParam::new(types::I64));
	let sig_ref = fn_builder.import_signature(sig);
	let deref = fn_builder.ins().iconst(types::I64, self.deref as i64);
	let deref_call = fn_builder.ins().call_indirect(sig_ref, deref, &[machine_state, n1]);
	let n1 = fn_builder.inst_results(deref_call)[0];

	let mut sig = module.make_signature();
	sig.call_conv = system_call_conv;
	sig.params.push(AbiParam::new(pointer_type));
	sig.params.push(AbiParam::new(types::I64));
	sig.returns.push(AbiParam::new(types::I64));
	let sig_ref = fn_builder.import_signature(sig);
	let store = fn_builder.ins().iconst(types::I64, self.store as i64);
	let store_call = fn_builder.ins().call_indirect(sig_ref, store, &[machine_state, n1]);
	fn_builder.inst_results(store_call)[0]
    }

    fn jit_get_number(&self, module: &JITModule, machine_state: Value, reg_ptr: Value, fn_builder: &mut FunctionBuilder, at: ArithmeticTerm) -> Value {
	let pointer_type = module.isa().pointer_type();
	let call_conv = module.isa().default_call_conv();
	
        match at {
	    ArithmeticTerm::Number(n) => {
		let n128 = unsafe { std::mem::transmute::<_, i128>(n) };
		let lo = fn_builder.ins().iconst(types::I64, n128 as i64);
		let hi = fn_builder.ins().iconst(types::I64, (n128 >> 64) as i64);
		fn_builder.ins().iconcat(lo, hi)			    
	    }
	    ArithmeticTerm::Interm(i) => {
		let interms_vec = fn_builder.ins().iadd_imm(machine_state, self.offset_interms as i64);
		let mut sig = module.make_signature();
		sig.call_conv = call_conv;
		sig.params.push(AbiParam::new(pointer_type));
		sig.returns.push(AbiParam::new(pointer_type));
		let sig_ref = fn_builder.import_signature(sig);
		let vec_ptr = fn_builder.ins().iconst(types::I64, self.vec_as_ptr as i64);
		let vec_ptr_call = fn_builder.ins().call_indirect(sig_ref, vec_ptr, &[interms_vec]);
		let interms = fn_builder.inst_results(vec_ptr_call)[0];
		fn_builder.ins().load(types::I128, MemFlags::new(), interms, Offset32::new((i as i32 - 1) * 16))
	    }
	    ArithmeticTerm::Reg(reg_type) => {
		let value = self.jit_store_deref_reg(&module, machine_state, reg_ptr, fn_builder, reg_type);
		let mut sig = module.make_signature();
		sig.call_conv = call_conv;
		sig.params.push(AbiParam::new(types::I64));
		sig.returns.push(AbiParam::new(types::I128));
		let sig_ref = fn_builder.import_signature(sig);
		let number_try_from = fn_builder.ins().iconst(types::I64, self.number_try_from as i64);
		let number_try_from_call = fn_builder.ins().call_indirect(sig_ref, number_try_from, &[value]);
		fn_builder.inst_results(number_try_from_call)[0]
	    }
	}
    }


    pub fn exec(&self, name: &str, machine_st: &mut MachineState) -> Result<(), ()> {
	if let Some(output) = self.modules.get(name) {
	    machine_st.p = machine_st.cp;
	    machine_st.oip = 0;
	    machine_st.iip = 0;
	    // machine_st.num_of_args = arity;
	    machine_st.num_of_args = 1;
	    machine_st.b0 = machine_st.b;
	    
	    (self.trampoline)(machine_st as *mut MachineState, machine_st.registers.as_ptr() as *mut Registers, output.code_ptr);
	    Ok(())
	} else {
	    Err(())
	}
    }
}

// basic.
#[test]
fn jit_test_proceed() {
    let mut machine_st = MachineState::new();
    let code = vec![Instruction::Proceed];
    let name = "basic/0";

    let mut jit = JitMachine::new();
    assert_eq!(jit.compile(name, code), Ok(()));
    jit.exec(name, &mut machine_st);
}

// basic.
// simple :- basic.
#[test]
fn jit_test_execute_named() {
    let mut machine_st = MachineState::new();
    let mut jit = JitMachine::new();
    let code = vec![Instruction::Proceed];
    let name = "basic/0";
    assert_eq!(jit.compile(name, code), Ok(()));

    let code = vec![Instruction::ExecuteNamed(0, atom!("basic"), CodeIndex::default(&mut Arena::new()))];
    let name = "simple/0";
    assert_eq!(jit.compile(name, code), Ok(()));
    jit.exec(name, &mut machine_st);
}

// a(5).
// b :- a(5).
#[test]
fn jit_test_get_constant() {
    let mut machine_st = MachineState::new();
    let mut jit = JitMachine::new();
    let code = vec![Instruction::GetConstant(Level::Shallow, fixnum_as_cell!(Fixnum::build_with(5)), RegType::Temp(1)), Instruction::Proceed];
    let name = "a/1";
    assert_eq!(jit.compile(name, code), Ok(()));

    let code = vec![Instruction::PutConstant(Level::Shallow, fixnum_as_cell!(Fixnum::build_with(5)), RegType::Temp(1)), Instruction::ExecuteNamed(1, atom!("a"), CodeIndex::default(&mut Arena::new()))];
    let name = "b/0";
    assert_eq!(jit.compile(name, code), Ok(()));
    jit.exec(name, &mut machine_st);
    assert_eq!(machine_st.fail, false);
}

// a(5).
// b :- a(6).
#[test]
fn jit_test_get_constant_fail() {
    let mut machine_st = MachineState::new();
    let mut jit = JitMachine::new();
    let code = vec![Instruction::GetConstant(Level::Shallow, fixnum_as_cell!(Fixnum::build_with(5)), RegType::Temp(1)), Instruction::Proceed];
    let name = "a/1";
    assert_eq!(jit.compile(name, code), Ok(()));

    let code = vec![Instruction::PutConstant(Level::Shallow, fixnum_as_cell!(Fixnum::build_with(6)), RegType::Temp(1)), Instruction::ExecuteNamed(1, atom!("a"), CodeIndex::default(&mut Arena::new()))];
    let name = "b/0";
    assert_eq!(jit.compile(name, code), Ok(()));
    jit.exec(name, &mut machine_st);
    assert_eq!(machine_st.fail, true);
}
