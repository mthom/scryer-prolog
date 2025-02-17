/* How does FFI work?

Each WAM machine has a ForeignFunctionTable instance that contains a table of functions and structs.

Structs are defined via foreign_struct/2. Basic types are defined by libffi, but struct types need to
be manually defined to get an ffi_type. Additionally, to recover structs from return arguments, we store
fields and atom_fields, as a way to lookup the content of the struct (fields) and the nested structs (atom_fields).

Functions are defined via use_foreign_module/2. It opens a library and leaks the memory of the library,
to prevent Rust freeing the memory. There's no way to recover that memory at the moment. We get a pointer for
each function and we build a CIF for each one, with the input arguments and the return argument.

Exec happens via '$foreign_call', we find the function, we try to cast the values that we have to the definition
of the function, we reserve memory for them and we build an array of pointers. To get the return argument, we
reserve enough memory for the return and we build the Scryer values from them.

Structs are a bit tricky as they need to be aligned. For that, we reserve enough memory (libffi calculates that)
and for each field: we add to the pointer until we're aligned to the next data type we're going to write, we write it,
and finally we add the pointer the size of what we've written.
*/

use crate::arena::Arena;
use crate::atom_table::Atom;
use crate::forms::Number;
use crate::parser::ast::Fixnum;

use dashu::Integer;
use libffi::middle::{Arg, Cif, CodePtr, Type};
use libloading::{Library, Symbol};
use ordered_float::OrderedFloat;
use std::alloc::{self, Layout};
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{c_void, CString};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Deref;
use std::ptr::NonNull;

pub struct FunctionDefinition {
    pub name: String,
    pub return_value: Atom,
    pub args: Vec<Atom>,
}

#[derive(Debug)]
pub struct FunctionImpl {
    cif: Cif,
    args: Vec<Type>,
    code_ptr: CodePtr,
    return_struct_name: Option<String>,
}

#[derive(Debug, Default)]
pub struct ForeignFunctionTable {
    table: HashMap<String, FunctionImpl>,
    structs: HashMap<String, StructImpl>,
}

#[derive(Clone, Debug)]
struct StructImpl {
    ffi_type: Type,
    fields: Vec<Type>,
    atom_fields: Vec<Atom>,
}

struct PointerArgs<'a, 'val> {
    memory: Vec<Arg>,
    phantom: PhantomData<&'a mut ArgValue<'val>>,
}

impl Deref for PointerArgs<'_, '_> {
    type Target = [Arg];

    fn deref(&self) -> &Self::Target {
        &self.memory
    }
}

enum ArgValue<'a> {
    U8(u8),
    I8(i8),
    U16(u16),
    I16(i16),
    U32(u32),
    I32(i32),
    U64(u64),
    I64(i64),
    F32(f32),
    F64(f64),
    Ptr(*mut c_void, PhantomData<&'a CString>),
    Struct(FfiStruct),
}

impl<'val> ArgValue<'val> {
    fn new(
        val: &'val mut Value,
        arg_type: &Type,
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<Self, FFIError> {
        match (unsafe { *arg_type.as_raw_ptr() }).type_ as u32 {
            libffi::raw::FFI_TYPE_UINT8 => Ok(Self::U8(val.as_int()?)),
            libffi::raw::FFI_TYPE_SINT8 => Ok(Self::I8(val.as_int()?)),
            libffi::raw::FFI_TYPE_UINT16 => Ok(Self::U16(val.as_int()?)),
            libffi::raw::FFI_TYPE_SINT16 => Ok(Self::I16(val.as_int()?)),
            libffi::raw::FFI_TYPE_UINT32 => Ok(Self::U32(val.as_int()?)),
            libffi::raw::FFI_TYPE_SINT32 => Ok(Self::I32(val.as_int()?)),
            libffi::raw::FFI_TYPE_UINT64 => Ok(Self::U64(val.as_int()?)),
            libffi::raw::FFI_TYPE_SINT64 => Ok(Self::I64(val.as_int()?)),
            libffi::raw::FFI_TYPE_FLOAT => Ok(Self::F32(val.as_float()? as f32)),
            libffi::raw::FFI_TYPE_DOUBLE => Ok(Self::F64(val.as_float()?)),
            libffi::raw::FFI_TYPE_POINTER => Ok(Self::Ptr(val.as_ptr()?, PhantomData)),
            libffi::raw::FFI_TYPE_STRUCT => Ok(Self::Struct(ForeignFunctionTable::build_struct(
                val,
                structs_table,
            )?)),
            _ => Err(FFIError::InvalidFFIType),
        }
    }

    fn build_args(
        args: &'val mut [Value],
        types: &[Type],
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<Vec<Self>, FFIError> {
        if types.len() != args.len() {
            return Err(FFIError::ArgCountMismatch);
        }

        args.iter_mut()
            .zip(types)
            .map(|(arg, arg_type)| ArgValue::new(arg, arg_type, structs_table))
            .collect::<Result<Vec<_>, _>>()
    }
}

struct FfiStruct {
    ptr: NonNull<c_void>,
    layout: Layout,
}

impl FfiStruct {
    fn new(layout: Layout) -> Result<Self, FFIError> {
        if let Some(ptr) = NonNull::new(unsafe { alloc::alloc(layout) as *mut c_void }) {
            Ok(FfiStruct { ptr, layout })
        } else {
            Err(FFIError::AllocationFailed)
        }
    }
}

impl Drop for FfiStruct {
    fn drop(&mut self) {
        unsafe { alloc::dealloc(self.ptr.as_ptr().cast(), self.layout) };
    }
}

impl ForeignFunctionTable {
    pub fn merge(&mut self, other: ForeignFunctionTable) {
        self.table.extend(other.table);
    }

    pub fn define_struct(&mut self, name: &str, atom_fields: Vec<Atom>) -> Result<(), FFIError> {
        let fields: Vec<_> = atom_fields
            .iter()
            .map(|x| self.map_type_ffi(x))
            .collect::<Result<_, _>>()?;
        let struct_type = libffi::middle::Type::structure(fields.iter().cloned());

        unsafe {
            // ensure that size and alignment of struct_type are set properly
            use libffi::low::{ffi_abi_FFI_DEFAULT_ABI, prep_cif};
            prep_cif(
                &mut Default::default(),
                ffi_abi_FFI_DEFAULT_ABI,
                1,
                struct_type.as_raw_ptr(),
                [struct_type.as_raw_ptr()].as_mut_ptr(),
            )
            .unwrap()
        };

        self.structs.insert(
            name.to_string(),
            StructImpl {
                ffi_type: struct_type,
                fields,
                atom_fields,
            },
        );
        Ok(())
    }

    fn map_type_ffi(&mut self, source: &Atom) -> Result<libffi::middle::Type, FFIError> {
        Ok(match source {
            atom!("sint64") | atom!("i64") => libffi::middle::Type::i64(),
            atom!("sint32") | atom!("i32") => libffi::middle::Type::i32(),
            atom!("sint16") | atom!("i16") => libffi::middle::Type::i16(),
            atom!("sint8") | atom!("i8") => libffi::middle::Type::i8(),
            atom!("uint64") | atom!("u64") => libffi::middle::Type::u64(),
            atom!("uint32") | atom!("u32") => libffi::middle::Type::u32(),
            atom!("uint16") | atom!("u16") => libffi::middle::Type::u16(),
            atom!("uint8") | atom!("u8") => libffi::middle::Type::u8(),
            atom!("bool") => libffi::middle::Type::i8(),
            atom!("void") => libffi::middle::Type::void(),
            atom!("cstr") => libffi::middle::Type::pointer(),
            atom!("ptr") => libffi::middle::Type::pointer(),
            atom!("f32") => libffi::middle::Type::f32(),
            atom!("f64") => libffi::middle::Type::f64(),
            struct_name => match self.structs.get_mut(&*struct_name.as_str()) {
                Some(ref mut struct_type) => struct_type.ffi_type.clone(),
                None => return Err(FFIError::InvalidFFIType),
            },
        })
    }

    pub(crate) fn load_library(
        &mut self,
        library_name: &str,
        functions: &Vec<FunctionDefinition>,
    ) -> Result<(), Box<dyn Error>> {
        let mut ff_table: ForeignFunctionTable = Default::default();
        unsafe {
            let library = Library::new(library_name)?;
            for function in functions {
                let symbol_name: CString = CString::new(function.name.clone())?;
                let code_ptr: Symbol<*mut c_void> = library.get(symbol_name.as_bytes_with_nul())?;
                let args: Vec<_> = function
                    .args
                    .iter()
                    .map(|x| self.map_type_ffi(x))
                    .collect::<Result<_, _>>()?;
                let result = self.map_type_ffi(&function.return_value)?;

                let cif = libffi::middle::Cif::new(args.iter().cloned(), result.clone());

                let return_struct_name =
                    if (*result.as_raw_ptr()).type_ as u32 == libffi::raw::FFI_TYPE_STRUCT {
                        Some(function.return_value.as_str().to_string())
                    } else {
                        None
                    };

                ff_table.table.insert(
                    function.name.clone(),
                    FunctionImpl {
                        cif,
                        args,
                        code_ptr: CodePtr(code_ptr.into_raw().as_raw_ptr()),
                        return_struct_name,
                    },
                );
            }
            std::mem::forget(library);
        }
        self.merge(ff_table);
        Ok(())
    }

    fn build_pointer_args<'args, 'val>(args: &[ArgValue<'val>]) -> PointerArgs<'args, 'val> {
        let args = args
            .iter()
            .map(|arg| match arg {
                ArgValue::U8(a) => libffi::middle::arg(a),
                ArgValue::I8(a) => libffi::middle::arg(a),
                ArgValue::U16(a) => libffi::middle::arg(a),
                ArgValue::I16(a) => libffi::middle::arg(a),
                ArgValue::U32(a) => libffi::middle::arg(a),
                ArgValue::I32(a) => libffi::middle::arg(a),
                ArgValue::U64(a) => libffi::middle::arg(a),
                ArgValue::I64(a) => libffi::middle::arg(a),
                ArgValue::F32(a) => libffi::middle::arg(a),
                ArgValue::F64(a) => libffi::middle::arg(a),
                ArgValue::Ptr(ptr, _) => unsafe { std::mem::transmute::<*mut c_void, Arg>(*ptr) },
                ArgValue::Struct(s) => unsafe {
                    std::mem::transmute::<*mut c_void, Arg>(s.ptr.as_ptr())
                },
            })
            .collect();

        PointerArgs {
            memory: args,
            phantom: PhantomData,
        }
    }

    fn build_struct(
        arg: &mut Value,
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<FfiStruct, FFIError> {
        let Value::Struct(ref name, ref mut struct_args) = arg else {
            return Err(FFIError::ValueCast);
        };

        let Some(struct_type) = structs_table.get(name) else {
            return Err(FFIError::InvalidStructName);
        };

        let args = ArgValue::build_args(struct_args, &struct_type.fields, structs_table)?;

        let ffi_type = unsafe { *struct_type.ffi_type.as_raw_ptr() };

        let alloc = FfiStruct::new(
            Layout::from_size_align(ffi_type.size, ffi_type.alignment.into()).unwrap(),
        )?;

        let Ok(mut current_layout) = Layout::from_size_align(0, 1) else {
            return Err(FFIError::AllocationFailed);
        };

        unsafe fn write_primitive<T>(
            ptr: NonNull<c_void>,
            layout: &mut Layout,
            val: T,
        ) -> Result<(), FFIError> {
            let (new_layout, offset) = layout
                .extend(Layout::new::<T>())
                .map_err(|_| FFIError::AllocationFailed)?;
            *layout = new_layout;
            ptr.byte_offset(offset as isize).cast::<T>().write(val);
            Ok(())
        }

        for arg in args {
            unsafe {
                match arg {
                    ArgValue::U8(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::I8(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::U16(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::I16(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::U32(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::I32(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::U64(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::I64(i) => write_primitive(alloc.ptr, &mut current_layout, i)?,
                    ArgValue::F32(f) => write_primitive(alloc.ptr, &mut current_layout, f)?,
                    ArgValue::F64(f) => write_primitive(alloc.ptr, &mut current_layout, f)?,
                    ArgValue::Ptr(p, _) => write_primitive(alloc.ptr, &mut current_layout, p)?,
                    ArgValue::Struct(arg) => {
                        let Ok((new_layout, offset)) = current_layout.extend(arg.layout) else {
                            return Err(FFIError::AllocationFailed);
                        };

                        current_layout = new_layout;

                        std::ptr::copy(
                            arg.ptr.as_ptr(),
                            alloc.ptr.byte_offset(offset as isize).as_ptr(),
                            arg.layout.size(),
                        );
                    }
                }
            }
        }

        if alloc.layout != current_layout.pad_to_align() {
            // sanity check
            return Err(FFIError::AllocationFailed);
        }

        Ok(alloc)
    }

    pub fn exec(
        &mut self,
        name: &str,
        mut args: Vec<Value>,
        arena: &mut Arena,
    ) -> Result<Value, FFIError> {
        let function_impl = self.table.get(name).ok_or(FFIError::FunctionNotFound)?;

        let args = ArgValue::build_args(&mut args, &function_impl.args, &self.structs)?;

        let args = Self::build_pointer_args(&args);

        macro_rules! call_and_return_int {
            ($type:ty) => {{
                let n = function_impl
                    .cif
                    .call::<$type>(function_impl.code_ptr, &args);
                Ok(Value::Number(fixnum!(Number, n, arena)))
            }};
        }

        macro_rules! call_and_return_float {
            ($type:ty) => {{
                let n = function_impl
                    .cif
                    .call::<$type>(function_impl.code_ptr, &args);
                Ok(Value::Number(Number::Float(OrderedFloat(f64::from(n)))))
            }};
        }

        let ffi_rtype = unsafe { *(*function_impl.cif.as_raw_ptr()).rtype };

        match ffi_rtype.type_ as u32 {
            libffi::raw::FFI_TYPE_VOID => {
                unsafe {
                    function_impl
                        .cif
                        .call::<c_void>(function_impl.code_ptr, &args)
                };
                Ok(Value::Number(Number::Fixnum(Fixnum::build_with(0))))
            }
            libffi::raw::FFI_TYPE_UINT8 => unsafe { call_and_return_int!(u8) },
            libffi::raw::FFI_TYPE_SINT8 => unsafe { call_and_return_int!(i8) },
            libffi::raw::FFI_TYPE_UINT16 => unsafe { call_and_return_int!(u16) },
            libffi::raw::FFI_TYPE_SINT16 => unsafe { call_and_return_int!(i16) },
            libffi::raw::FFI_TYPE_UINT32 => unsafe { call_and_return_int!(u32) },
            libffi::raw::FFI_TYPE_SINT32 => unsafe { call_and_return_int!(i32) },
            libffi::raw::FFI_TYPE_UINT64 => unsafe { call_and_return_int!(u64) },
            libffi::raw::FFI_TYPE_SINT64 => unsafe { call_and_return_int!(i64) },
            libffi::raw::FFI_TYPE_POINTER => {
                let ptr = unsafe {
                    function_impl
                        .cif
                        .call::<*mut c_void>(function_impl.code_ptr, &args)
                };
                Ok(Value::Number(fixnum!(Number, ptr as isize, arena)))
            }
            libffi::raw::FFI_TYPE_FLOAT => unsafe { call_and_return_float!(f32) },
            libffi::raw::FFI_TYPE_DOUBLE => unsafe { call_and_return_float!(f64) },
            libffi::raw::FFI_TYPE_STRUCT => {
                let name = function_impl
                    .return_struct_name
                    .as_ref()
                    .ok_or(FFIError::StructNotFound)?;
                let struct_type = self.structs.get(name).ok_or(FFIError::StructNotFound)?;
                let ffi_type = unsafe { *struct_type.ffi_type.as_raw_ptr() };

                let layout =
                    Layout::from_size_align(ffi_type.size, ffi_type.alignment.into()).unwrap();

                let alloc = FfiStruct::new(layout)?;

                let ptr_args: &[Arg] = &args;

                unsafe {
                    libffi::raw::ffi_call(
                        function_impl.cif.as_raw_ptr(),
                        Some(*function_impl.code_ptr.as_safe_fun()),
                        alloc.ptr.as_ptr(),
                        ptr_args.as_ptr() as *mut *mut c_void,
                    )
                };
                let struct_val = self.read_struct(alloc.ptr.as_ptr(), name, struct_type, arena);

                drop(alloc);

                struct_val
            }
            _ => unreachable!(),
        }
    }

    fn read_struct(
        &self,
        ptr: *mut c_void,
        name: &str,
        struct_type: &StructImpl,
        arena: &mut Arena,
    ) -> Result<Value, FFIError> {
        unsafe {
            let mut returns = Vec::new();
            let mut field_ptr = ptr;

            for (field, type_name) in struct_type.fields.iter().zip(&struct_type.atom_fields) {
                macro_rules! read_and_push_int {
                    ($type:ty) => {{
                        field_ptr =
                            field_ptr.add(field_ptr.align_offset(std::mem::align_of::<$type>()));
                        let n = std::ptr::read(field_ptr as *mut $type);
                        returns.push(Value::Number(fixnum!(Number, n, arena)));
                        field_ptr = field_ptr.add(std::mem::size_of::<$type>());
                    }};
                }

                match (*field.as_raw_ptr()).type_ as u32 {
                    libffi::raw::FFI_TYPE_UINT8 => read_and_push_int!(u8),
                    libffi::raw::FFI_TYPE_SINT8 => read_and_push_int!(i8),
                    libffi::raw::FFI_TYPE_UINT16 => read_and_push_int!(u16),
                    libffi::raw::FFI_TYPE_SINT16 => read_and_push_int!(i16),
                    libffi::raw::FFI_TYPE_UINT32 => read_and_push_int!(u32),
                    libffi::raw::FFI_TYPE_SINT32 => read_and_push_int!(i32),
                    libffi::raw::FFI_TYPE_UINT64 => read_and_push_int!(u64),
                    libffi::raw::FFI_TYPE_SINT64 => read_and_push_int!(i64),
                    libffi::raw::FFI_TYPE_POINTER => read_and_push_int!(i64),
                    libffi::raw::FFI_TYPE_FLOAT => {
                        field_ptr =
                            field_ptr.add(field_ptr.align_offset(std::mem::align_of::<f32>()));
                        let n: f32 = std::ptr::read(field_ptr as *mut f32);
                        returns.push(Value::Number(Number::Float(OrderedFloat(n.into()))));
                        field_ptr = field_ptr.add(std::mem::size_of::<f32>());
                    }
                    libffi::raw::FFI_TYPE_DOUBLE => {
                        field_ptr =
                            field_ptr.add(field_ptr.align_offset(std::mem::align_of::<f64>()));
                        let n: f64 = std::ptr::read(field_ptr as *mut f64);
                        returns.push(Value::Number(Number::Float(OrderedFloat(n))));
                        field_ptr = field_ptr.add(std::mem::size_of::<f64>());
                    }
                    libffi::raw::FFI_TYPE_STRUCT => {
                        let substruct = type_name.as_str();
                        let struct_type = self
                            .structs
                            .get(&*substruct)
                            .ok_or(FFIError::StructNotFound)?;
                        let ffi_type = *struct_type.ffi_type.as_raw_ptr();
                        field_ptr =
                            field_ptr.add(field_ptr.align_offset(ffi_type.alignment as usize));
                        let struct_val =
                            self.read_struct(field_ptr, &substruct, struct_type, arena);
                        returns.push(struct_val?);
                        field_ptr = field_ptr.add(ffi_type.size);
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
            Ok(Value::Struct(name.into(), returns))
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Number(Number),
    CString(CString),
    Struct(String, Vec<Value>),
}

impl Value {
    fn as_int<I>(&self) -> Result<I, FFIError>
    where
        Integer: TryInto<I>,
        i64: TryInto<I>,
    {
        match self {
            Value::Number(Number::Integer(ibig_ptr)) => {
                let ibig: &Integer = ibig_ptr;
                ibig.clone().try_into().map_err(|_| FFIError::ValueDontFit)
            }
            Value::Number(Number::Fixnum(fixnum)) => fixnum
                .get_num()
                .try_into()
                .map_err(|_| FFIError::ValueDontFit),
            _ => Err(FFIError::ValueCast),
        }
    }

    fn as_float(&self) -> Result<f64, FFIError> {
        match self {
            &Value::Number(Number::Float(OrderedFloat(f))) => Ok(f),
            _ => Err(FFIError::ValueCast),
        }
    }

    fn as_ptr(&mut self) -> Result<*mut c_void, FFIError> {
        match self {
            Value::CString(ref mut cstr) => Ok(&mut *cstr as *mut _ as *mut c_void),
            Value::Number(Number::Fixnum(fixnum)) => Ok(std::ptr::with_exposed_provenance_mut(
                fixnum.get_num() as usize,
            )),
            _ => Err(FFIError::ValueCast),
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
    ArgCountMismatch,
    AllocationFailed,
}

impl std::fmt::Display for FFIError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl Error for FFIError {}
