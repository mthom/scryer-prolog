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
use crate::parser::ast::{Fixnum, MightNotFitInFixnum};

use dashu::Integer;
use libffi::middle::{Arg, Cif, CodePtr, Type};
use libloading::{Library, Symbol};
use ordered_float::OrderedFloat;
use std::alloc::{self, Layout};
use std::collections::HashMap;
use std::error::Error;
use std::ffi::{c_char, c_void, CStr, CString};
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
    args: Vec<FfiType>,
    code_ptr: CodePtr,
    return_type: FfiType,
}

impl FunctionImpl {
    unsafe fn call_void(&self, args: &[Arg], _: &mut Arena) -> Result<Value, FfiError> {
        self.cif.call::<()>(self.code_ptr, args);
        Ok(Value::Number(Number::Fixnum(Fixnum::build_with(0))))
    }

    unsafe fn call_int<T>(&self, args: &[Arg], arena: &mut Arena) -> Result<Value, FfiError>
    where
        Integer: From<T>,
        T: Copy + TryInto<i64> + MightNotFitInFixnum,
    {
        let n = self.cif.call::<T>(self.code_ptr, args);
        Ok(Value::Number(fixnum!(Number, n, arena)))
    }

    unsafe fn call_float<T>(&self, args: &[Arg], _: &mut Arena) -> Result<Value, FfiError>
    where
        T: Into<f64>,
    {
        let n = self.cif.call::<T>(self.code_ptr, args);
        Ok(Value::Number(Number::Float(OrderedFloat(n.into()))))
    }

    unsafe fn call_ptr(&self, args: &[Arg], arena: &mut Arena) -> Result<Value, FfiError> {
        let ptr = unsafe { self.cif.call::<*mut c_void>(self.code_ptr, args) };
        Ok(Value::Number(fixnum!(Number, ptr as isize, arena)))
    }

    unsafe fn call_cstr(&self, args: &[Arg], _: &mut Arena) -> Result<Value, FfiError> {
        let ptr = unsafe { self.cif.call::<*mut c_char>(self.code_ptr, args) };
        Ok(Value::CString(unsafe { CStr::from_ptr(ptr) }.to_owned()))
    }

    unsafe fn call_struct(
        &self,
        return_type_name: Atom,
        args: &[Arg],
        arena: &mut Arena,
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<Value, FfiError> {
        let struct_type = structs_table
            .get(&*return_type_name.as_str())
            .ok_or(FfiError::StructNotFound)?;
        let ffi_type = unsafe { *struct_type.ffi_type.as_raw_ptr() };

        let layout = Layout::from_size_align(ffi_type.size, ffi_type.alignment.into())
            .map_err(|_| FfiError::LayoutError)?;

        let alloc = FfiStruct::new(layout)?;

        unsafe {
            libffi::raw::ffi_call(
                self.cif.as_raw_ptr(),
                Some(*self.code_ptr.as_safe_fun()),
                alloc.ptr.as_ptr(),
                args.as_ptr() as *mut *mut c_void,
            )
        };

        let struct_val = struct_type.read(
            alloc.ptr.as_ptr(),
            &return_type_name.as_str(),
            structs_table,
            arena,
        );

        drop(alloc);

        struct_val
    }

    fn call(
        &self,
        args: &[Arg],
        arena: &mut Arena,
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<Value, FfiError> {
        let call_fn: unsafe fn(&Self, &[Arg], &mut Arena) -> Result<Value, FfiError> =
            match self.return_type {
                FfiType::Void => FunctionImpl::call_void,
                FfiType::U8 => FunctionImpl::call_int::<u8>,
                FfiType::I8 | FfiType::Bool => FunctionImpl::call_int::<i8>,
                FfiType::U16 => FunctionImpl::call_int::<u16>,
                FfiType::I16 => FunctionImpl::call_int::<i16>,
                FfiType::U32 => FunctionImpl::call_int::<u32>,
                FfiType::I32 => FunctionImpl::call_int::<i32>,
                FfiType::U64 => FunctionImpl::call_int::<u64>,
                FfiType::I64 => FunctionImpl::call_int::<i64>,
                FfiType::F32 => FunctionImpl::call_float::<f32>,
                FfiType::F64 => FunctionImpl::call_float::<f64>,
                FfiType::Ptr => FunctionImpl::call_ptr,
                FfiType::CStr => FunctionImpl::call_cstr,
                FfiType::Struct(name) => {
                    return unsafe { self.call_struct(name, args, arena, structs_table) }
                }
            };
        unsafe { call_fn(self, args, arena) }
    }
}

#[derive(Debug, Default)]
pub struct ForeignFunctionTable {
    table: HashMap<String, FunctionImpl>,
    structs: HashMap<String, StructImpl>,
}

#[derive(Clone, Debug)]
struct StructImpl {
    ffi_type: Type,
    fields: Vec<FfiType>,
}

impl StructImpl {
    fn build(
        &self,
        structs_table: &HashMap<String, StructImpl>,
        struct_args: &mut [Value],
    ) -> Result<FfiStruct, FfiError> {
        let args = ArgValue::build_args(struct_args, &self.fields, structs_table)?;

        let ffi_type = unsafe { *self.ffi_type.as_raw_ptr() };

        let alloc = FfiStruct::new(
            Layout::from_size_align(ffi_type.size, ffi_type.alignment.into())
                .map_err(|_| FfiError::LayoutError)?,
        )?;

        let Ok(mut current_layout) = Layout::from_size_align(0, 1) else {
            return Err(FfiError::LayoutError);
        };

        unsafe fn write_primitive<T>(
            ptr: NonNull<c_void>,
            layout: &mut Layout,
            val: T,
        ) -> Result<(), FfiError> {
            let (new_layout, offset) = layout
                .extend(Layout::new::<T>())
                .map_err(|_| FfiError::LayoutError)?;
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
                            return Err(FfiError::LayoutError);
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
            return Err(FfiError::LayoutError);
        }

        Ok(alloc)
    }

    fn read(
        &self,
        ptr: *mut c_void,
        struct_name: &str,
        struct_table: &HashMap<String, StructImpl>,
        arena: &mut Arena,
    ) -> Result<Value, FfiError> {
        unsafe {
            let mut returns = Vec::new();

            unsafe fn read_primitive<T>(
                ptr: *mut c_void,
                layout: &mut Layout,
            ) -> Result<T, FfiError> {
                let (new_layout, offset) = layout
                    .extend(Layout::new::<T>())
                    .map_err(|_| FfiError::LayoutError)?;
                *layout = new_layout;
                let n = std::ptr::read::<T>(ptr.byte_offset(offset as isize).cast());
                Ok(n)
            }

            unsafe fn read_int<T>(
                ptr: *mut c_void,
                layout: &mut Layout,
                arena: &mut Arena,
            ) -> Result<Value, FfiError>
            where
                T: Copy + TryInto<i64> + MightNotFitInFixnum,
                Integer: From<T>,
            {
                let n = read_primitive::<T>(ptr, layout)?;
                Ok(Value::Number(fixnum!(Number, n, arena)))
            }

            unsafe fn read_float<T>(
                ptr: *mut c_void,
                layout: &mut Layout,
            ) -> Result<Value, FfiError>
            where
                T: Into<f64>,
            {
                let n = read_primitive::<T>(ptr, layout)?;
                Ok(Value::Number(Number::Float(OrderedFloat(n.into()))))
            }

            let mut layout = Layout::from_size_align(0, 1).map_err(|_| FfiError::LayoutError)?;

            for field_type in &self.fields {
                let val = match field_type {
                    FfiType::U8 => read_int::<u8>(ptr, &mut layout, arena),
                    FfiType::I8 | FfiType::Bool => read_int::<i8>(ptr, &mut layout, arena),
                    FfiType::U16 => read_int::<u16>(ptr, &mut layout, arena),
                    FfiType::I16 => read_int::<i16>(ptr, &mut layout, arena),
                    FfiType::U32 => read_int::<u32>(ptr, &mut layout, arena),
                    FfiType::I32 => read_int::<i32>(ptr, &mut layout, arena),
                    FfiType::U64 => read_int::<u64>(ptr, &mut layout, arena),
                    FfiType::I64 => read_int::<i64>(ptr, &mut layout, arena),
                    FfiType::Ptr => {
                        let ptr = read_primitive::<*mut c_void>(ptr, &mut layout)?;
                        Ok(Value::Number(fixnum!(Number, ptr as isize, arena)))
                    }
                    FfiType::CStr => {
                        let ptr = read_primitive::<*mut c_void>(ptr, &mut layout)?;
                        Ok(Value::CString(CStr::from_ptr(ptr.cast()).to_owned()))
                    }
                    FfiType::F32 => read_float::<f32>(ptr, &mut layout),
                    FfiType::F64 => read_float::<f64>(ptr, &mut layout),
                    FfiType::Struct(substruct) => {
                        let Some(substruct_type) = struct_table.get(&*substruct.as_str()) else {
                            return Err(FfiError::StructNotFound);
                        };

                        let ffi_type = *substruct_type.ffi_type.as_raw_ptr();
                        let field_layout =
                            Layout::from_size_align(ffi_type.size, ffi_type.alignment as usize)
                                .map_err(|_| FfiError::LayoutError)?;
                        let (new_layout, offset) = layout
                            .extend(field_layout)
                            .map_err(|_| FfiError::LayoutError)?;
                        layout = new_layout;
                        let field_ptr = ptr.byte_offset(offset as isize);
                        let struct_val = substruct_type.read(
                            field_ptr,
                            &substruct.as_str(),
                            struct_table,
                            arena,
                        )?;
                        Ok(struct_val)
                    }
                    FfiType::Void => unreachable!("void is not a valid field type"),
                };
                returns.push(val?);
            }
            Ok(Value::Struct(struct_name.to_string(), returns))
        }
    }
}

struct PointerArgs<'a, 'val> {
    memory: Vec<Arg>,
    phantom: PhantomData<&'a mut ArgValue<'val>>,
}

impl<'args, 'val> PointerArgs<'args, 'val> {
    fn new(args: &'args [ArgValue<'val>]) -> Self {
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
}

impl Deref for PointerArgs<'_, '_> {
    type Target = [Arg];

    fn deref(&self) -> &Self::Target {
        &self.memory
    }
}

#[derive(Debug, Clone, Copy)]
enum FfiType {
    Void,
    Bool,
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    F32,
    F64,
    Ptr,
    CStr,
    Struct(Atom),
}

impl FfiType {
    fn from_atom(atom: &Atom) -> Self {
        match atom {
            atom!("sint64") | atom!("i64") => Self::I64,
            atom!("sint32") | atom!("i32") => Self::I32,
            atom!("sint16") | atom!("i16") => Self::I16,
            atom!("sint8") | atom!("i8") => Self::I8,
            atom!("uint64") | atom!("u64") => Self::U64,
            atom!("uint32") | atom!("u32") => Self::U32,
            atom!("uint16") | atom!("u16") => Self::U16,
            atom!("uint8") | atom!("u8") => Self::U8,
            atom!("bool") => Self::Bool,
            atom!("void") => Self::Void,
            atom!("cstr") => Self::CStr,
            atom!("ptr") => Self::Ptr,
            atom!("f32") => Self::F32,
            atom!("f64") => Self::F64,
            struct_name => Self::Struct(*struct_name),
        }
    }

    fn to_type(self, structs_table: &HashMap<String, StructImpl>) -> Result<Type, FfiError> {
        Ok(match self {
            Self::I64 => libffi::middle::Type::i64(),
            Self::I32 => libffi::middle::Type::i32(),
            Self::I16 => libffi::middle::Type::i16(),
            Self::I8 => libffi::middle::Type::i8(),
            Self::U64 => libffi::middle::Type::u64(),
            Self::U32 => libffi::middle::Type::u32(),
            Self::U16 => libffi::middle::Type::u16(),
            Self::U8 => libffi::middle::Type::u8(),
            Self::Bool => libffi::middle::Type::i8(),
            Self::Void => libffi::middle::Type::void(),
            Self::CStr => libffi::middle::Type::pointer(),
            Self::Ptr => libffi::middle::Type::pointer(),
            Self::F32 => libffi::middle::Type::f32(),
            Self::F64 => libffi::middle::Type::f64(),
            Self::Struct(struct_name) => structs_table
                .get(&*struct_name.as_str())
                .ok_or(FfiError::StructNotFound)?
                .ffi_type
                .clone(),
        })
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
        arg_type: &FfiType,
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<Self, FfiError> {
        match arg_type {
            FfiType::U8 => Ok(Self::U8(val.as_int()?)),
            FfiType::I8 | FfiType::Bool => Ok(Self::I8(val.as_int()?)),
            FfiType::U16 => Ok(Self::U16(val.as_int()?)),
            FfiType::I16 => Ok(Self::I16(val.as_int()?)),
            FfiType::U32 => Ok(Self::U32(val.as_int()?)),
            FfiType::I32 => Ok(Self::I32(val.as_int()?)),
            FfiType::U64 => Ok(Self::U64(val.as_int()?)),
            FfiType::I64 => Ok(Self::I64(val.as_int()?)),
            FfiType::F32 => Ok(Self::F32(val.as_float()? as f32)),
            FfiType::F64 => Ok(Self::F64(val.as_float()?)),
            FfiType::Ptr => Ok(Self::Ptr(val.as_ptr()?, PhantomData)),
            FfiType::CStr => Ok(Self::Ptr(val.as_ptr()?, PhantomData)),
            FfiType::Struct(atom) => {
                let (name, args) = val.as_struct()?;

                if &*atom.as_str() != name {
                    return Err(FfiError::ValueCast);
                }

                let Some(struct_type) = structs_table.get(name) else {
                    return Err(FfiError::StructNotFound);
                };

                Ok(Self::Struct(struct_type.build(structs_table, args)?))
            }
            FfiType::Void => Err(FfiError::InvalidArgumentType),
        }
    }

    fn build_args(
        args: &'val mut [Value],
        types: &[FfiType],
        structs_table: &HashMap<String, StructImpl>,
    ) -> Result<Vec<Self>, FfiError> {
        if types.len() != args.len() {
            return Err(FfiError::ArgCountMismatch);
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
    fn new(layout: Layout) -> Result<Self, FfiError> {
        if let Some(ptr) = NonNull::new(unsafe { alloc::alloc(layout) as *mut c_void }) {
            Ok(FfiStruct { ptr, layout })
        } else {
            Err(FfiError::AllocationFailed)
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

    pub fn define_struct(&mut self, name: &str, atom_fields: Vec<Atom>) -> Result<(), FfiError> {
        let fields: Vec<_> = atom_fields.iter().map(FfiType::from_atom).collect();
        let struct_type = libffi::middle::Type::structure(
            fields
                .iter()
                .map(|field| field.to_type(&self.structs))
                .collect::<Result<Vec<_>, _>>()?,
        );

        unsafe {
            // ensure that size and alignment of struct_type are set properly
            use libffi::low::{ffi_abi_FFI_DEFAULT_ABI, prep_cif};
            prep_cif(
                &mut Default::default(),
                ffi_abi_FFI_DEFAULT_ABI,
                1,
                struct_type.as_raw_ptr(),
                [struct_type.as_raw_ptr()].as_mut_ptr(),
            )?;
        };

        self.structs.insert(
            name.to_string(),
            StructImpl {
                ffi_type: struct_type,
                fields,
            },
        );
        Ok(())
    }

    pub(crate) fn load_library(
        &mut self,
        library_name: &str,
        functions: &Vec<FunctionDefinition>,
    ) -> Result<(), Box<dyn Error>> {
        let mut ff_table: ForeignFunctionTable = Default::default();
        let library = unsafe { Library::new(library_name) }?;
        for function in functions {
            let symbol_name: CString = CString::new(function.name.clone())?;
            let code_ptr: Symbol<*mut c_void> =
                unsafe { library.get(symbol_name.as_bytes_with_nul()) }?;
            let args: Vec<_> = function.args.iter().map(FfiType::from_atom).collect();
            let return_type = FfiType::from_atom(&function.return_value);

            let cif = libffi::middle::Cif::new(
                args.iter()
                    .map(|arg| arg.to_type(&self.structs))
                    .collect::<Result<Vec<_>, _>>()?,
                return_type.to_type(&self.structs)?,
            );

            ff_table.table.insert(
                function.name.clone(),
                FunctionImpl {
                    cif,
                    args,
                    code_ptr: CodePtr(unsafe { code_ptr.into_raw() }.as_raw_ptr()),
                    return_type,
                },
            );
        }
        std::mem::forget(library);
        self.merge(ff_table);
        Ok(())
    }

    pub fn exec(
        &mut self,
        fn_name: &str,
        mut args: Vec<Value>,
        arena: &mut Arena,
    ) -> Result<Value, FfiError> {
        let fn_impl = self.table.get(fn_name).ok_or(FfiError::FunctionNotFound)?;

        let args = ArgValue::build_args(&mut args, &fn_impl.args, &self.structs)?;

        let args = PointerArgs::new(&args);

        fn_impl.call(&args, arena, &self.structs)
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Number(Number),
    CString(CString),
    Struct(String, Vec<Value>),
}

impl Value {
    fn as_int<I>(&self) -> Result<I, FfiError>
    where
        Integer: TryInto<I>,
        i64: TryInto<I>,
    {
        match self {
            Value::Number(Number::Integer(ibig_ptr)) => {
                let ibig: &Integer = ibig_ptr;
                ibig.clone()
                    .try_into()
                    .map_err(|_| FfiError::ValueOutOfRange)
            }
            Value::Number(Number::Fixnum(fixnum)) => fixnum
                .get_num()
                .try_into()
                .map_err(|_| FfiError::ValueOutOfRange),
            _ => Err(FfiError::ValueCast),
        }
    }

    fn as_float(&self) -> Result<f64, FfiError> {
        match self {
            &Value::Number(Number::Float(OrderedFloat(f))) => Ok(f),
            _ => Err(FfiError::ValueCast),
        }
    }

    fn as_ptr(&mut self) -> Result<*mut c_void, FfiError> {
        match self {
            Value::CString(ref mut cstr) => Ok(&mut *cstr as *mut _ as *mut c_void),
            Value::Number(Number::Fixnum(fixnum)) => Ok(std::ptr::with_exposed_provenance_mut(
                fixnum.get_num() as usize,
            )),
            _ => Err(FfiError::ValueCast),
        }
    }

    fn as_struct(&mut self) -> Result<(&str, &mut [Self]), FfiError> {
        match self {
            Value::Struct(name, values) => Ok((name, values)),
            _ => Err(FfiError::ValueCast),
        }
    }
}

#[derive(Debug)]
pub enum FfiError {
    ValueCast,
    ValueOutOfRange,
    InvalidArgumentType,
    InvalidArgument,
    InvalidFfiType,
    InvalidStruct,
    FunctionNotFound,
    StructNotFound,
    ArgCountMismatch,
    AllocationFailed,
    // LayoutError should never occour
    LayoutError,
    UnsupportedAbi,
}

impl std::fmt::Display for FfiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl Error for FfiError {}

impl From<libffi::low::Error> for FfiError {
    fn from(value: libffi::low::Error) -> Self {
        match value {
            libffi::low::Error::Typedef => FfiError::InvalidFfiType,
            libffi::low::Error::Abi => FfiError::UnsupportedAbi,
        }
    }
}
