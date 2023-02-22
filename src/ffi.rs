use crate::atom_table::Atom;

use std::alloc::{alloc, Layout};
use std::any::Any;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{CString, c_void};
use std::convert::TryFrom;

use libffi::low::{ffi_cif, types, CodePtr, ffi_abi_FFI_DEFAULT_ABI, prep_cif, ffi_type, type_tag};
use libloading::{Symbol, Library};

pub struct FunctionDefinition {
    pub name: String,
    pub return_value: Atom,
    pub args: Vec<Atom>,
}

#[derive(Debug)]
pub struct FunctionImpl {
    cif: ffi_cif,
    args: Vec<*mut ffi_type>,
    code_ptr: CodePtr,
    return_struct_name: Option<String>,
}

#[derive(Debug, Default)]
pub struct ForeignFunctionTable {
    table: HashMap<String, FunctionImpl>,
    structs: HashMap<String, StructImpl>,
}

#[derive(Debug)]
struct StructImpl {
    ffi_type: ffi_type,
    fields: Vec<*mut ffi_type>,
}

struct PointerArgs {
    pointers: Vec<*mut c_void>,
    memory: Vec<Box<dyn Any>>,
}

impl ForeignFunctionTable {
    pub fn merge(&mut self, other: ForeignFunctionTable) {
	self.table.extend(other.table);
    }

    pub fn define_struct(&mut self, name: &str, fields: Vec<Atom>) {
	let mut fields: Vec<_> = fields.iter().map(|x| self.map_type_ffi(&x)).collect();
	fields.push(std::ptr::null_mut::<ffi_type>());
	let mut struct_type: ffi_type = Default::default();
	struct_type.type_ = type_tag::STRUCT;
	struct_type.elements = fields.as_mut_ptr();
	self.structs.insert(name.to_string(), StructImpl { ffi_type: struct_type, fields});
    }

    fn map_type_ffi(&mut self, source: &Atom) -> *mut ffi_type {
	unsafe {
	match source {
	    atom!("sint64") => &mut types::sint64,
	    atom!("sint32") => &mut types::sint32,
	    atom!("sint16") => &mut types::sint16,
	    atom!("sint8") => &mut types::sint8,
	    atom!("uint64") => &mut types::uint64,
	    atom!("uint32") => &mut types::uint32,
	    atom!("uint16") => &mut types::uint16,
	    atom!("uint8") => &mut types::uint8,
	    atom!("bool") => &mut types::sint8,
	    atom!("void") => &mut types::void,
	    atom!("cstr") => &mut types::pointer,
	    atom!("ptr") => &mut types::pointer,
	    atom!("f32") => &mut types::float,
	    atom!("f64") => &mut types::double,
	    struct_name => {
		match self.structs.get_mut(struct_name.as_str()) {
		    Some(ref mut struct_type) => {
			&mut struct_type.ffi_type
		    },
		    None => unreachable!()
		}
	    }
	}
	}
    }

    pub(crate) fn load_library(&mut self, library_name: &str, functions: &Vec<FunctionDefinition>) -> Result<(), Box<dyn Error>> {
	let mut ff_table: ForeignFunctionTable = Default::default();
	unsafe {
	    let library = Library::new(library_name)?;
	    for function in functions {
		let symbol_name: CString = CString::new(function.name.clone())?;
		let code_ptr: Symbol<*mut c_void> = library.get(&symbol_name.into_bytes_with_nul())?;
		let mut args: Vec<_> = function.args.iter().map(|x| self.map_type_ffi(&x)).collect();
		let mut cif: ffi_cif = Default::default();
		prep_cif(
		    &mut cif,
		    ffi_abi_FFI_DEFAULT_ABI,
		    args.len(),
		    self.map_type_ffi(&function.return_value),
		    args.as_mut_ptr()
		).unwrap();

		let return_struct_name = if (*self.map_type_ffi(&function.return_value)).type_ as u32 == libffi::raw::FFI_TYPE_STRUCT {
		    Some(function.return_value.as_str().to_string())
		} else {
		    None
		};

		ff_table.table.insert(function.name.clone(), FunctionImpl {
		    cif,
		    args,
		    code_ptr: CodePtr(code_ptr.into_raw().into_raw() as *mut _),
		    return_struct_name,
		});
	    }
	    std::mem::forget(library);
	}
	self.merge(ff_table);
	Ok(())
    }

    fn build_pointer_args(mut args: &mut Vec<Value>, type_args: &Vec<*mut ffi_type>, structs_table: &mut HashMap<String, StructImpl>) -> Result<PointerArgs, FFIError> {
	let mut pointers = Vec::with_capacity(args.len());
	let mut memory = Vec::new();
	for i in 0..args.len() {
	    let field_type = type_args[i];
	    unsafe {
		match (*field_type).type_ as u32 {
		    libffi::raw::FFI_TYPE_UINT8 => {
			let n: u8 = u8::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_SINT8 => {
			let n: i8 = i8::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_UINT16 => {
			let n: u16 = u16::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_SINT16 => {
			let n: i16 = i16::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_UINT32 => {
			let n: u32 = u32::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_SINT32 => {
			let n: i32 = i32::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_UINT64 => {
			let n: u64 = u64::try_from(args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_SINT64 => {
			let n: i64 = args[i].as_int()?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_FLOAT => {
			let n: f32 = args[i].as_float()? as f32;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_DOUBLE => {
			let n: f64 = args[i].as_float()?;
			let mut box_value = Box::new(n) as Box<dyn Any>;
			pointers.push(&mut *box_value as *mut _ as *mut c_void);
			memory.push(box_value);
		    },
		    libffi::raw::FFI_TYPE_POINTER => {
			let ptr: *mut c_void = args[i].as_ptr()?;
			pointers.push(ptr);
		    },
		    libffi::raw::FFI_TYPE_STRUCT => {
			match args[i] {
			    Value::Struct(ref name, ref struct_args) => {
				if let Some(ref mut struct_type) = structs_table.get_mut(name) {
				    let layout = Layout::from_size_align(struct_type.ffi_type.size, struct_type.ffi_type.alignment.into()).unwrap();
				    let ptr = alloc(layout) as *mut c_void;
				    let mut field_ptr = ptr;
				    for i in 0..(struct_type.fields.len()-1) {
					let field = struct_type.fields[i];
					match (*field).type_ as u32 {
					    libffi::raw::FFI_TYPE_UINT8 => {
						let n: u8 = u8::try_from(struct_args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
						std::ptr::write(field_ptr as *mut u8, n);
						field_ptr = field_ptr.add(std::mem::size_of::<u8>());
					    },
					    libffi::raw::FFI_TYPE_UINT32 => {
						let n: u32 = u32::try_from(struct_args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
						std::ptr::write(field_ptr as *mut u32, n);
						field_ptr = field_ptr.add(std::mem::size_of::<u32>());
					    },
					    libffi::raw::FFI_TYPE_SINT32 => {
						let n: u32 = u32::try_from(struct_args[i].as_int()?).map_err(|_| FFIError::ValueDontFit)?;
						std::ptr::write(field_ptr as *mut u32, n);
						field_ptr = field_ptr.add(std::mem::size_of::<u32>());
					    },					    
					    libffi::raw::FFI_TYPE_FLOAT => {
						let n: f32 = struct_args[i].as_float()? as f32;
						std::ptr::write(field_ptr as *mut f32, n);
						field_ptr = field_ptr.add(std::mem::size_of::<f32>());
					    },
					    _ => {
						unreachable!()
					    }
					}
				    }
				    pointers.push(ptr);
				    memory.push(Box::from_raw(ptr));
				} else {
				    return Err(FFIError::InvalidStructName);
				}
			    }
			    _ => return Err(FFIError::ValueCast)
			}
		    },
		    _ => return Err(FFIError::InvalidFFIType)
		}
	    }
	}
	Ok(PointerArgs {
	    pointers,
	    memory
	})
    }

    pub fn exec(&mut self, name: &str, mut args: Vec<Value>) -> Result<Value, FFIError> {
	let function_impl = self.table.get_mut(name).ok_or(FFIError::FunctionNotFound)?;
	let mut pointer_args = Self::build_pointer_args(&mut args, &function_impl.args, &mut self.structs).unwrap();
	return unsafe {
	    match (*function_impl.cif.rtype).type_ as u32 {
		libffi::raw::FFI_TYPE_VOID => {
		    let mut _n: Box<i32> = Box::new(0);
		    libffi::raw::ffi_call(
			&mut function_impl.cif,
			Some(*function_impl.code_ptr.as_safe_fun()),
			&mut *_n as *mut _ as *mut c_void,
			pointer_args.pointers.as_mut_ptr() as *mut *mut c_void
		    );
		    Ok(Value::Int(0))
		},
		libffi::raw::FFI_TYPE_SINT8 => {
		    let mut n: Box<i8> = Box::new(0);
		    libffi::raw::ffi_call(
			&mut function_impl.cif,
			Some(*function_impl.code_ptr.as_safe_fun()),
			&mut *n as *mut _ as *mut c_void,
			pointer_args.pointers.as_mut_ptr() as *mut *mut c_void
		    );
		    Ok(Value::Int(i64::from(*n)))
		},		    
		libffi::raw::FFI_TYPE_SINT32 => {
		    let mut n: Box<i32> = Box::new(0);
		    libffi::raw::ffi_call(
			&mut function_impl.cif,
			Some(*function_impl.code_ptr.as_safe_fun()),
			&mut *n as *mut _ as *mut c_void,
			pointer_args.pointers.as_mut_ptr() as *mut *mut c_void
		    );
		    Ok(Value::Int(i64::from(*n)))
		},
		libffi::raw::FFI_TYPE_STRUCT => {
		    let mut returns = Vec::new();
		    let mut struct_type = self.structs.get_mut(&function_impl.return_struct_name.clone().ok_or(FFIError::StructNotFound)?).ok_or(FFIError::StructNotFound)?;
		    let layout = Layout::from_size_align(struct_type.ffi_type.size, struct_type.ffi_type.alignment.into()).unwrap();
		    let ptr = alloc(layout) as *mut c_void;
		    libffi::raw::ffi_call(
			&mut function_impl.cif,
			Some(*function_impl.code_ptr.as_safe_fun()),
			&mut *ptr as *mut _ as *mut c_void,
			pointer_args.pointers.as_mut_ptr() as *mut *mut c_void
		    );

		    let mut field_ptr = ptr;
		    for i in 0..(struct_type.fields.len()-1) {
			let field = struct_type.fields[i];
			match (*field).type_ as u32 {
			    libffi::raw::FFI_TYPE_UINT8 => {
				let n = std::ptr::read(field_ptr as *mut u8);
				returns.push(Value::Int(i64::from(n)));
				field_ptr = field_ptr.add(std::mem::size_of::<u8>());
			    },
			    libffi::raw::FFI_TYPE_SINT32 => {
				let n = std::ptr::read(field_ptr as *mut i32);
				returns.push(Value::Int(i64::from(n)));
				field_ptr = field_ptr.add(std::mem::size_of::<i32>());
			    },
			    libffi::raw::FFI_TYPE_UINT32 => {
				let n = std::ptr::read(field_ptr as *mut u32);
				returns.push(Value::Int(i64::from(n)));
				field_ptr = field_ptr.add(std::mem::size_of::<u32>());
			    },
			    _ => {
				unreachable!()
			    }
			}
		    }
		    drop(Box::from_raw(ptr));
		    Ok(Value::Struct("texture".into(), returns))
		},
	    _ => unreachable!()
	    }
	};
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    CString(CString),
    Struct(String, Vec<Value>),
}

impl Value {
    fn as_int(&self) -> Result<i64, FFIError> {
	match self {
	    Value::Int(n) => Ok(*n),
	    _ => Err(FFIError::ValueCast),
	}
    }

    fn as_float(&self) -> Result<f64, FFIError> {
	match self {
	    Value::Float(n) => Ok(*n),
	    Value::Int(n) => Ok(*n as f64),
	    _ => Err(FFIError::ValueCast),
	}
    }

    fn as_ptr(&mut self) -> Result<*mut c_void, FFIError> {
	match self {
	    Value::CString(ref mut cstr) => Ok(&mut *cstr as *mut _ as *mut c_void),
	    Value::Int(n) => Ok(*n as *mut c_void),
	    _ => Err(FFIError::ValueCast)
	}
    }
}

#[derive(Debug)]
pub enum FFIError {
    ValueCast,
    ValueDontFit,
    InvalidFFIType,
    InvalidStructName,
    FunctionNotFound,
    StructNotFound,
}
