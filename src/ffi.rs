//! Types and Traits used for interacting with foreign functions from prolog

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
use crate::atom_table::{Atom, AtomTable};
use crate::forms::Number;
use crate::functor_macro::FunctorElement;
use crate::machine::heap::{sized_iter_to_heap_list, Heap};
use crate::machine::machine_errors::DomainErrorType;
use crate::parser::ast::{Fixnum, MightNotFitInFixnum};
use crate::{LeafAnswer, Machine, Term};

use dashu::Integer;
use libffi::middle::{Arg, Cif, CodePtr, FfiAbi, Type};
use libloading::{Library, Symbol};
use ordered_float::OrderedFloat;
use std::alloc::{self, Layout};
use std::collections::{HashMap, TryReserveError};
use std::error::Error;
use std::ffi::{c_char, c_void, CStr, CString};
use std::fmt::Debug;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::ptr::NonNull;

/// An enum for specifying the calling convention (ABI) to be used
pub enum FfiCallingConvention {
    /// Use the targets/platforms default calling convention (ABI)
    Default,
    // explicit abi value see the ffi_abi_*_ABI constants at
    // <https://docs.rs/libffi-sys/latest/src/libffi_sys/arch.rs.html>
    // NOTE: the availability and numbering differs by target/platform !!!!!!
    // i.e. on x86_win32 value 2 is STDCALL but on x86_64 its UNIX64
    // #[cfg(feature = "unstable_ffi")]
    /// Use the specified calling convention (ABI)
    Explicit(FfiAbi),
}

/// A struct representing a function type
pub struct FnType {
    /// the calling convention of the function
    #[allow(dead_code)] // used with unstable_ffi feature
    pub(crate) calling_convention: FfiCallingConvention,
    /// the arguments of the function
    pub(crate) args: Vec<FfiType>,
    // the return type of the function
    pub(crate) ret: FfiType,
}

pub(crate) struct FunctionDefinition {
    // The name used for looking up the function in the dynamic/shard libray
    // - using a CString rather than an Atom so that is guaranteed to not contain a nul byte
    pub(crate) symbol: CString,
    // The name used for calling the function from prolog
    pub(crate) name: Atom,
    pub(crate) fn_type: FnType,
}

#[derive(Debug)]
pub(crate) struct FunctionImpl {
    cif: Cif,
    args: Vec<FfiType>,
    code_ptr: CodePtr,
    return_type: FfiType,
}

impl FunctionImpl {
    fn new(
        ptr: *const c_void,
        fn_type: &FnType,
        structs_table: &HashMap<Atom, StructImpl>,
    ) -> Result<Self, StructNotFoundError> {
        #[allow(unused_mut)] // mut is necessary when unstable_ffi feature is enabled
        let mut cif = libffi::middle::Cif::new(
            fn_type
                .args
                .iter()
                .map(|arg| arg.to_type(structs_table))
                .collect::<Result<Vec<_>, _>>()?,
            fn_type.ret.to_type(structs_table)?,
        );

        #[cfg(feature = "unstable_ffi")]
        if let FfiCallingConvention::Explicit(conv) = fn_type.calling_convention {
            cif.set_abi(conv);
        }

        let fn_impl = FunctionImpl {
            cif,
            args: fn_type.args.clone(),
            code_ptr: CodePtr(ptr.cast_mut()),
            return_type: fn_type.ret,
        };
        Ok(fn_impl)
    }

    unsafe fn call_void(&self, args: &[Arg], _: &mut Arena) -> Result<Value, FfiUseError> {
        self.cif.call::<()>(self.code_ptr, args);
        Ok(Value::Number(Number::Fixnum(Fixnum::build_with(0))))
    }

    unsafe fn call_int<T>(&self, args: &[Arg], arena: &mut Arena) -> Result<Value, FfiUseError>
    where
        Integer: From<T>,
        T: Copy + TryInto<i64> + MightNotFitInFixnum,
    {
        let n = self.cif.call::<T>(self.code_ptr, args);
        Ok(Value::Number(fixnum!(Number, n, arena)))
    }

    unsafe fn call_float<T>(&self, args: &[Arg], _: &mut Arena) -> Result<Value, FfiUseError>
    where
        T: Into<f64>,
    {
        let n = self.cif.call::<T>(self.code_ptr, args);
        Ok(Value::Number(Number::Float(OrderedFloat(n.into()))))
    }

    unsafe fn call_ptr(&self, args: &[Arg], arena: &mut Arena) -> Result<Value, FfiUseError> {
        let ptr = unsafe { self.cif.call::<*mut c_void>(self.code_ptr, args) };
        Ok(Value::Number(fixnum!(Number, ptr as isize, arena)))
    }

    unsafe fn call_cstr(&self, args: &[Arg], _: &mut Arena) -> Result<Value, FfiUseError> {
        let ptr = unsafe {
            self.cif
                .call::<Option<NonNull<c_char>>>(self.code_ptr, args)
        };

        if let Some(cstr) = ptr {
            Ok(Value::CString(
                unsafe { CStr::from_ptr(cstr.as_ptr()) }.to_owned(),
            ))
        } else {
            Ok(Value::Number(Number::Fixnum(Fixnum::build_with(0))))
        }
    }

    unsafe fn call_struct(
        &self,
        return_type_name: Atom,
        args: &[Arg],
        arena: &mut Arena,
        structs_table: &HashMap<Atom, StructImpl>,
    ) -> Result<Value, FfiUseError> {
        let struct_type = structs_table
            .get(&return_type_name)
            .ok_or(FfiUseError::StructNotFound(return_type_name))?;
        let ffi_type = unsafe { *struct_type.ffi_type.as_raw_ptr() };

        let layout = Layout::from_size_align(ffi_type.size, ffi_type.alignment.into())
            .map_err(|_| FfiUseError::LayoutError)?;

        let alloc = FfiStruct::new(layout, FfiAllocator::Rust)?;

        unsafe {
            libffi::raw::ffi_call(
                self.cif.as_raw_ptr(),
                Some(*self.code_ptr.as_safe_fun()),
                alloc.ptr.as_ptr(),
                args.as_ptr() as *mut *mut c_void,
            )
        };

        let struct_val =
            struct_type.read(alloc.ptr.as_ptr(), return_type_name, structs_table, arena);

        drop(alloc);

        struct_val
    }

    fn call(
        &self,
        args: &[Arg],
        arena: &mut Arena,
        structs_table: &HashMap<Atom, StructImpl>,
    ) -> Result<Value, FfiUseError> {
        let call_fn: unsafe fn(&Self, &[Arg], &mut Arena) -> Result<Value, FfiUseError> =
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
pub(crate) struct ForeignFunctionTable {
    table: HashMap<Atom, FunctionImpl>,
    structs: HashMap<Atom, StructImpl>,
}

#[derive(Clone, Debug)]
struct StructImpl {
    ffi_type: Type,
    fields: Vec<FfiType>,
}

impl StructImpl {
    fn layout(&self) -> Result<Layout, FfiUseError> {
        let ffi_type = unsafe { *self.ffi_type.as_raw_ptr() };
        Layout::from_size_align(ffi_type.size, ffi_type.alignment.into())
            .map_err(|_| FfiUseError::LayoutError)
    }

    fn build(
        &self,
        struct_name: Atom,
        structs_table: &HashMap<Atom, StructImpl>,
        struct_args: &mut [Value],
    ) -> Result<FfiStruct, FfiUseError> {
        let args = ArgValue::build_args(
            struct_name,
            ArgCountMismatchKind::Struct,
            struct_args,
            &self.fields,
            structs_table,
        )?;

        let alloc = FfiStruct::new(self.layout()?, FfiAllocator::Rust)?;

        let Ok(mut current_layout) = Layout::from_size_align(0, 1) else {
            return Err(FfiUseError::LayoutError);
        };

        unsafe fn write_primitive<T>(
            ptr: NonNull<c_void>,
            layout: &mut Layout,
            val: T,
        ) -> Result<(), FfiUseError> {
            let (new_layout, offset) = layout
                .extend(Layout::new::<T>())
                .map_err(|_| FfiUseError::LayoutError)?;
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
                            return Err(FfiUseError::LayoutError);
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
            return Err(FfiUseError::LayoutError);
        }

        Ok(alloc)
    }

    fn read(
        &self,
        ptr: *mut c_void,
        struct_name: Atom,
        struct_table: &HashMap<Atom, StructImpl>,
        arena: &mut Arena,
    ) -> Result<Value, FfiUseError> {
        unsafe {
            let mut returns = Vec::new();

            unsafe fn read_primitive<T>(
                ptr: *mut c_void,
                layout: &mut Layout,
            ) -> Result<T, FfiUseError> {
                let (new_layout, offset) = layout
                    .extend(Layout::new::<T>())
                    .map_err(|_| FfiUseError::LayoutError)?;
                *layout = new_layout;
                let n = std::ptr::read::<T>(ptr.byte_offset(offset as isize).cast());
                Ok(n)
            }

            unsafe fn read_int<T>(
                ptr: *mut c_void,
                layout: &mut Layout,
                arena: &mut Arena,
            ) -> Result<Value, FfiUseError>
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
            ) -> Result<Value, FfiUseError>
            where
                T: Into<f64>,
            {
                let n = read_primitive::<T>(ptr, layout)?;
                Ok(Value::Number(Number::Float(OrderedFloat(n.into()))))
            }

            let mut layout = Layout::from_size_align(0, 1).map_err(|_| FfiUseError::LayoutError)?;

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
                        let Some(substruct_type) = struct_table.get(substruct) else {
                            return Err(FfiUseError::StructNotFound(*substruct));
                        };

                        let ffi_type = *substruct_type.ffi_type.as_raw_ptr();
                        let field_layout =
                            Layout::from_size_align(ffi_type.size, ffi_type.alignment as usize)
                                .map_err(|_| FfiUseError::LayoutError)?;
                        let (new_layout, offset) = layout
                            .extend(field_layout)
                            .map_err(|_| FfiUseError::LayoutError)?;
                        layout = new_layout;
                        let field_ptr = ptr.byte_offset(offset as isize);
                        let struct_val =
                            substruct_type.read(field_ptr, *substruct, struct_table, arena)?;
                        Ok(struct_val)
                    }
                    FfiType::Void => return Err(FfiUseError::VoidArgumentType),
                };
                returns.push(val?);
            }
            Ok(Value::Struct(struct_name, returns))
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
                ArgValue::Ptr(ptr, _) => Arg::new(ptr),
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
#[non_exhaustive]
#[allow(missing_docs)]
pub enum FfiType {
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
    fn to_atom(self) -> Atom {
        match self {
            FfiType::Void => atom!("void"),
            FfiType::Bool => atom!("bool"),
            FfiType::U8 => atom!("u8"),
            FfiType::I8 => atom!("i8"),
            FfiType::U16 => atom!("u16"),
            FfiType::I16 => atom!("i16"),
            FfiType::U32 => atom!("u32"),
            FfiType::I32 => atom!("i32"),
            FfiType::U64 => atom!("u64"),
            FfiType::I64 => atom!("i64"),
            FfiType::F32 => atom!("f32"),
            FfiType::F64 => atom!("f64"),
            FfiType::Ptr => atom!("ptr"),
            FfiType::CStr => atom!("cstr"),
            FfiType::Struct(atom) => atom,
        }
    }
}

trait ToFfiType {
    const TYPE: FfiType;
}

macro_rules! impl_to_ffi_type {
    ($($t:ty => $v:ident);*$(;)?) => {
        $(
            impl ToFfiType for $t {
                const TYPE: FfiType = FfiType::$v;
            }

            impl FfiTypeable for $t {
                fn to_type(_machine: &mut Machine) -> FfiType {
                    Self::TYPE
                }
            }
        )*
    };
}

impl_to_ffi_type!(
    u8 => U8;
    i8 => I8;
    u16 => U16;
    i16 => I16;
    u32 => U32;
    i32 => I32;
    u64 => U64;
    i64 => I64;
    f32 => F32;
    f64 => F64;
);

impl FfiType {
    pub(crate) fn from_atom(atom: Atom) -> Self {
        match atom {
            atom!("char") => <core::ffi::c_char as ToFfiType>::TYPE,
            atom!("uchar") => <core::ffi::c_uchar as ToFfiType>::TYPE,
            atom!("schar") => <core::ffi::c_schar as ToFfiType>::TYPE,
            atom!("short") => <core::ffi::c_short as ToFfiType>::TYPE,
            atom!("ushort") => <core::ffi::c_ushort as ToFfiType>::TYPE,
            atom!("int") => <core::ffi::c_int as ToFfiType>::TYPE,
            atom!("uint") => <core::ffi::c_uint as ToFfiType>::TYPE,
            atom!("long") => <core::ffi::c_long as ToFfiType>::TYPE,
            atom!("ulong") => <core::ffi::c_ulong as ToFfiType>::TYPE,
            atom!("longlong") => <core::ffi::c_longlong as ToFfiType>::TYPE,
            atom!("ulonglong") => <core::ffi::c_ulonglong as ToFfiType>::TYPE,
            atom!("float") => <core::ffi::c_float as ToFfiType>::TYPE,
            atom!("double") => <core::ffi::c_double as ToFfiType>::TYPE,
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
            struct_name => Self::Struct(struct_name),
        }
    }

    fn to_type(
        self,
        structs_table: &HashMap<Atom, StructImpl>,
    ) -> Result<Type, StructNotFoundError> {
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
                .get(&struct_name)
                .ok_or(StructNotFoundError(struct_name))?
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
        structs_table: &HashMap<Atom, StructImpl>,
    ) -> Result<Self, FfiUseError> {
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
            FfiType::Struct(arg_type_name) => {
                let (val_type_name, args) = val.as_struct()?;

                if *arg_type_name != val_type_name {
                    return Err(FfiUseError::ValueCast(*arg_type_name, val_type_name));
                }

                let Some(struct_type) = structs_table.get(&val_type_name) else {
                    return Err(FfiUseError::StructNotFound(*arg_type_name));
                };

                Ok(Self::Struct(struct_type.build(
                    *arg_type_name,
                    structs_table,
                    args,
                )?))
            }
            FfiType::Void => Err(FfiUseError::VoidArgumentType),
        }
    }

    fn build_args(
        name: Atom,
        kind: ArgCountMismatchKind,
        args: &'val mut [Value],
        types: &[FfiType],
        structs_table: &HashMap<Atom, StructImpl>,
    ) -> Result<Vec<Self>, FfiUseError> {
        if types.len() != args.len() {
            return Err(FfiUseError::ArgCountMismatch {
                name,
                kind,
                expected: types.len(),
                got: args.len(),
            });
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
    allocator: FfiAllocator,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum FfiAllocator {
    Rust,
    C,
}

impl TryFrom<Atom> for FfiAllocator {
    type Error = ();

    fn try_from(value: Atom) -> Result<Self, Self::Error> {
        match value {
            atom!("rust") => Ok(Self::Rust),
            atom!("c") => Ok(Self::C),
            _ => Err(()),
        }
    }
}

impl FfiAllocator {
    /// # Safety
    ///
    /// - layout must not have a size of 0
    unsafe fn alloc(self, layout: Layout) -> Result<NonNull<c_void>, FfiUseError> {
        let ptr = match self {
            FfiAllocator::Rust => unsafe { alloc::alloc(layout).cast() },
            FfiAllocator::C => unsafe { libc::malloc(layout.size()) },
        };

        NonNull::new(ptr).ok_or(FfiUseError::AllocationFailed)
    }

    /// # Safety
    ///
    /// - ptr must point to an allocation currently allocated by this allocator
    /// - layout must match the layout that was used to allocate the allocation pointed to by ptr
    unsafe fn dealloc(self, layout: Layout, ptr: NonNull<c_void>) {
        match self {
            FfiAllocator::Rust => unsafe { alloc::dealloc(ptr.as_ptr().cast(), layout) },
            FfiAllocator::C => unsafe { libc::free(ptr.as_ptr()) },
        }
    }
}

impl FfiStruct {
    fn new(layout: Layout, allocator: FfiAllocator) -> Result<Self, FfiUseError> {
        assert_ne!(layout.size(), 0);
        Ok(FfiStruct {
            ptr: unsafe { allocator.alloc(layout) }?,
            layout,
            allocator,
        })
    }
}

impl Drop for FfiStruct {
    fn drop(&mut self) {
        unsafe { self.allocator.dealloc(self.layout, self.ptr) };
    }
}

impl ForeignFunctionTable {
    pub(crate) fn merge(&mut self, other: ForeignFunctionTable) {
        self.table.extend(other.table);
    }

    pub(crate) fn define_struct(
        &mut self,
        name: Atom,
        fields: Vec<FfiType>,
    ) -> Result<(), FfiSetupError> {
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
            name,
            StructImpl {
                ffi_type: struct_type,
                fields,
            },
        );
        Ok(())
    }

    pub(crate) fn define_function(
        &mut self,
        name: Atom,
        fn_ptr: *mut c_void,
        fn_type: &FnType,
    ) -> Result<(), StructNotFoundError> {
        let fn_impl = FunctionImpl::new(fn_ptr, fn_type, &self.structs)?;
        self.table.insert(name, fn_impl);
        Ok(())
    }

    pub(crate) fn load_library(
        &mut self,
        library_name: &str,
        functions: &Vec<FunctionDefinition>,
    ) -> Result<(), FfiLoadLibraryError> {
        let mut ff_table: ForeignFunctionTable = Default::default();
        let library = unsafe { Library::new(library_name) }
            .map_err(|err| FfiLoadLibraryError::LibLoadingError(library_name.to_string(), err))?;
        for function in functions {
            let code_ptr: Symbol<*mut c_void> =
                unsafe { library.get(function.symbol.as_bytes_with_nul()) }.map_err(|err| {
                    FfiLoadLibraryError::LibLoadingError(
                        function.symbol.to_string_lossy().to_string(),
                        err,
                    )
                })?;

            // Safety:
            // - if a failure occurs before all functions have been looked up the temporary ff_table is droppedn and fn_ptr is never used
            // - if no failure occurs we forget the library ensuring it is never dropped before we merge the temporary ff_table into self
            let fn_ptr = unsafe { code_ptr.into_raw() }.as_raw_ptr();

            let fn_impl = FunctionImpl::new(fn_ptr, &function.fn_type, &self.structs)?;
            ff_table.table.insert(function.name, fn_impl);
        }
        std::mem::forget(library);
        self.merge(ff_table);
        Ok(())
    }

    pub(crate) fn exec(
        &self,
        fn_name: Atom,
        mut args: Vec<Value>,
        arena: &mut Arena,
    ) -> Result<Value, FfiUseError> {
        let fn_impl = self
            .table
            .get(&fn_name)
            .ok_or(FfiUseError::FunctionNotFound(fn_name, args.len()))?;

        let args = ArgValue::build_args(
            fn_name,
            ArgCountMismatchKind::Function,
            &mut args,
            &fn_impl.args,
            &self.structs,
        )?;

        let args = PointerArgs::new(&args);

        fn_impl.call(&args, arena, &self.structs)
    }

    pub(crate) fn allocate(
        &self,
        allocator: FfiAllocator,
        kind: FfiType,
        mut args: Value,
        arena: &mut Arena,
    ) -> Result<Value, FfiUseError> {
        fn allocate_primitive<T: Copy>(
            allocator: FfiAllocator,
            initial_value: T,
            arena: &mut Arena,
        ) -> Result<Value, FfiUseError> {
            const { assert!(std::mem::size_of::<T>() != 0) };
            let ptr = unsafe { allocator.alloc(Layout::new::<T>()) }?;
            unsafe { ptr.cast::<T>().write(initial_value) };
            Ok(Value::Number(fixnum!(
                Number,
                ptr.as_ptr().expose_provenance(),
                arena
            )))
        }

        match kind {
            FfiType::Void => Err(FfiUseError::VoidArgumentType),
            FfiType::Bool => {
                let val = args.as_int::<i8>()?;
                let init = match val {
                    0 => false,
                    1 => true,
                    _ => {
                        return Err(FfiUseError::ValueOutOfRange(
                            DomainErrorType::ZeroOrOne,
                            args,
                        ))
                    }
                };
                allocate_primitive::<bool>(allocator, init, arena)
            }
            FfiType::U8 => allocate_primitive::<u8>(allocator, args.as_int()?, arena),
            FfiType::I8 => allocate_primitive::<i8>(allocator, args.as_int()?, arena),
            FfiType::U16 => allocate_primitive::<u16>(allocator, args.as_int()?, arena),
            FfiType::I16 => allocate_primitive::<i16>(allocator, args.as_int()?, arena),
            FfiType::U32 => allocate_primitive::<u32>(allocator, args.as_int()?, arena),
            FfiType::I32 => allocate_primitive::<i32>(allocator, args.as_int()?, arena),
            FfiType::U64 => allocate_primitive::<u64>(allocator, args.as_int()?, arena),
            FfiType::I64 => allocate_primitive::<i64>(allocator, args.as_int()?, arena),
            FfiType::F32 => allocate_primitive::<f32>(allocator, args.as_float()? as f32, arena),
            FfiType::F64 => allocate_primitive::<f64>(allocator, args.as_float()?, arena),
            FfiType::Ptr => allocate_primitive::<*mut c_void>(allocator, args.as_ptr()?, arena),
            FfiType::CStr => Err(FfiUseError::CStrFieldType),
            FfiType::Struct(struct_name) => {
                let Some(struct_impl) = self.structs.get(&struct_name) else {
                    return Err(FfiUseError::StructNotFound(struct_name));
                };

                let (_, args) = args.as_struct()?;

                let ffi_struct = struct_impl.build(struct_name, &self.structs, args)?;

                let ptr = ManuallyDrop::new(ffi_struct).ptr;

                Ok(Value::Number(fixnum!(
                    Number,
                    ptr.as_ptr().expose_provenance(),
                    arena
                )))
            }
        }
    }

    pub(crate) fn read_ptr(
        &self,
        kind: FfiType,
        mut ptr: Value,
        arena: &mut Arena,
    ) -> Result<Value, FfiUseError> {
        unsafe fn read_int<T>(ptr: NonNull<c_void>, arena: &mut Arena) -> Value
        where
            T: Copy + TryInto<i64> + MightNotFitInFixnum,
            Integer: From<T>,
        {
            let n = ptr.cast::<T>().read();
            Value::Number(fixnum!(Number, n, arena))
        }

        let ptr = ptr.as_ptr()?;

        let Some(ptr) = NonNull::new(ptr) else {
            return Err(FfiUseError::NullPtr);
        };

        match kind {
            FfiType::Void => Err(FfiUseError::VoidArgumentType),
            FfiType::U8 => Ok(unsafe { read_int::<u8>(ptr, arena) }),
            FfiType::Bool | FfiType::I8 => Ok(unsafe { read_int::<i8>(ptr, arena) }),
            FfiType::U16 => Ok(unsafe { read_int::<u16>(ptr, arena) }),
            FfiType::I16 => Ok(unsafe { read_int::<i16>(ptr, arena) }),
            FfiType::U32 => Ok(unsafe { read_int::<u32>(ptr, arena) }),
            FfiType::I32 => Ok(unsafe { read_int::<i32>(ptr, arena) }),
            FfiType::U64 => Ok(unsafe { read_int::<u64>(ptr, arena) }),
            FfiType::I64 => Ok(unsafe { read_int::<i64>(ptr, arena) }),
            FfiType::F32 => Ok(Value::Number(Number::Float(
                (unsafe { ptr.cast::<f32>().read() } as f64).into(),
            ))),
            FfiType::F64 => Ok(Value::Number(Number::Float(
                unsafe { ptr.cast::<f64>().read() }.into(),
            ))),
            FfiType::Ptr => {
                let addr = unsafe { ptr.cast::<*mut c_void>().read() }.expose_provenance();
                Ok(Value::Number(fixnum!(Number, addr, arena)))
            }
            FfiType::CStr => Ok(Value::CString(
                unsafe { CStr::from_ptr(ptr.as_ptr().cast()) }.to_owned(),
            )),
            FfiType::Struct(struct_name) => {
                let Some(struct_impl) = self.structs.get(&struct_name) else {
                    return Err(FfiUseError::StructNotFound(struct_name));
                };

                struct_impl.read(ptr.as_ptr(), struct_name, &self.structs, arena)
            }
        }
    }

    pub(crate) fn deallocate(
        &self,
        allocator: FfiAllocator,
        kind: FfiType,
        mut ptr: Value,
    ) -> Result<(), FfiUseError> {
        fn deallocate_primitive<T: Copy>(allocator: FfiAllocator, ptr: NonNull<c_void>) {
            const { assert!(std::mem::size_of::<T>() != 0) };
            unsafe { allocator.dealloc(Layout::new::<T>(), ptr) };
        }

        let ptr = ptr.as_ptr()?;

        let Some(ptr) = NonNull::new(ptr) else {
            return Err(FfiUseError::NullPtr);
        };

        match kind {
            FfiType::Void => return Err(FfiUseError::VoidArgumentType),
            FfiType::Bool => deallocate_primitive::<bool>(allocator, ptr),
            FfiType::U8 => deallocate_primitive::<u8>(allocator, ptr),
            FfiType::I8 => deallocate_primitive::<i8>(allocator, ptr),
            FfiType::U16 => deallocate_primitive::<u16>(allocator, ptr),
            FfiType::I16 => deallocate_primitive::<i16>(allocator, ptr),
            FfiType::U32 => deallocate_primitive::<u32>(allocator, ptr),
            FfiType::I32 => deallocate_primitive::<i32>(allocator, ptr),
            FfiType::U64 => deallocate_primitive::<u64>(allocator, ptr),
            FfiType::I64 => deallocate_primitive::<i64>(allocator, ptr),
            FfiType::F32 => deallocate_primitive::<f32>(allocator, ptr),
            FfiType::F64 => deallocate_primitive::<f64>(allocator, ptr),
            FfiType::Ptr => deallocate_primitive::<*mut c_void>(allocator, ptr),
            FfiType::CStr => return Err(FfiUseError::CStrFieldType),
            FfiType::Struct(struct_name) => {
                let Some(struct_impl) = self.structs.get(&struct_name) else {
                    return Err(FfiUseError::StructNotFound(struct_name));
                };

                let layout = struct_impl.layout()?;

                drop(FfiStruct {
                    ptr,
                    layout,
                    allocator,
                })
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) enum Value {
    Number(Number),
    CString(CString),
    Struct(Atom, Vec<Value>),
}

impl Value {
    fn as_int<I>(&self) -> Result<I, FfiUseError>
    where
        Integer: TryInto<I>,
        i64: TryInto<I>,
    {
        match self {
            Value::Number(Number::Integer(ibig_ptr)) => {
                let ibig: &Integer = ibig_ptr;
                ibig.clone().try_into().map_err(|_| {
                    FfiUseError::ValueOutOfRange(DomainErrorType::FixedSizedInt, self.clone())
                })
            }
            Value::Number(Number::Fixnum(fixnum)) => fixnum.get_num().try_into().map_err(|_| {
                FfiUseError::ValueOutOfRange(DomainErrorType::FixedSizedInt, self.clone())
            }),
            _ => Err(FfiUseError::ValueOutOfRange(
                DomainErrorType::FixedSizedInt,
                self.clone(),
            )),
        }
    }

    fn as_float(&self) -> Result<f64, FfiUseError> {
        match self {
            &Value::Number(Number::Float(OrderedFloat(f))) => Ok(f),
            _ => Err(FfiUseError::ValueOutOfRange(
                DomainErrorType::F64,
                self.clone(),
            )),
        }
    }

    fn as_ptr(&mut self) -> Result<*mut c_void, FfiUseError> {
        match self {
            Value::CString(ref mut cstr) => Ok(cstr.as_ptr().cast_mut().cast()),
            Value::Number(Number::Fixnum(fixnum)) => Ok(std::ptr::with_exposed_provenance_mut(
                fixnum.get_num() as usize,
            )),
            _ => Err(FfiUseError::ValueOutOfRange(
                DomainErrorType::PtrLike,
                self.clone(),
            )),
        }
    }

    fn as_struct(&mut self) -> Result<(Atom, &mut [Self]), FfiUseError> {
        match self {
            Value::Struct(name, values) => Ok((*name, values)),
            _ => Err(FfiUseError::ValueOutOfRange(
                DomainErrorType::FfiStruct,
                self.clone(),
            )),
        }
    }
}

#[derive(Debug)]
pub(crate) enum FfiLoadLibraryError {
    SetupError(FfiSetupError),
    LibLoadingError(String, libloading::Error),
}

impl From<FfiSetupError> for FfiLoadLibraryError {
    fn from(value: FfiSetupError) -> Self {
        Self::SetupError(value)
    }
}

impl From<StructNotFoundError> for FfiLoadLibraryError {
    fn from(value: StructNotFoundError) -> Self {
        Self::SetupError(value.into())
    }
}

#[derive(Debug)]
pub(crate) struct StructNotFoundError(Atom);

/// An enum for different errors that can occure during FFI setup
/// i.e. type/function declaration
#[derive(Debug)]
#[non_exhaustive]
pub enum FfiSetupError {
    /// A struct type was encountered that has not yet been defined
    StructNotFound(Atom),
    /// Tried to define an unsupported type definition
    UnsupportedTypedef,
    /// Attempted to use an unsupported calling convention (ABI)
    UnsupportedAbi,
    /// An allocation failed
    AllocationFailed,
}

impl From<TryReserveError> for FfiSetupError {
    fn from(_: TryReserveError) -> Self {
        Self::AllocationFailed
    }
}

impl From<StructNotFoundError> for FfiSetupError {
    fn from(StructNotFoundError(name): StructNotFoundError) -> Self {
        Self::StructNotFound(name)
    }
}

impl From<libffi::low::Error> for FfiSetupError {
    fn from(value: libffi::low::Error) -> Self {
        match value {
            libffi::low::Error::Typedef => FfiSetupError::UnsupportedTypedef,
            libffi::low::Error::Abi => FfiSetupError::UnsupportedAbi,
        }
    }
}

impl std::fmt::Display for FfiSetupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl Error for FfiSetupError {}

#[derive(Debug)]
pub(crate) enum FfiUseError {
    ValueCast(Atom, Atom),
    ValueOutOfRange(DomainErrorType, Value),
    VoidArgumentType,
    FunctionNotFound(Atom, usize),
    StructNotFound(Atom),
    ArgCountMismatch {
        name: Atom, // ffi function or struct
        kind: ArgCountMismatchKind,
        expected: usize,
        got: usize,
    },
    AllocationFailed,
    // LayoutError should never occour
    LayoutError,
    CStrFieldType,
    NullPtr,
}

#[derive(Debug)]
pub(crate) enum FfiError {
    LibLoading(String, libloading::Error),
    Setup(FfiSetupError),
    Use(FfiUseError),
    InvalidSymbol(Atom),
}

impl From<FfiSetupError> for FfiError {
    fn from(value: FfiSetupError) -> Self {
        Self::Setup(value)
    }
}

impl From<FfiUseError> for FfiError {
    fn from(value: FfiUseError) -> Self {
        Self::Use(value)
    }
}

impl From<FfiLoadLibraryError> for FfiError {
    fn from(value: FfiLoadLibraryError) -> Self {
        match value {
            FfiLoadLibraryError::SetupError(ffi_setup_error) => Self::Setup(ffi_setup_error),
            FfiLoadLibraryError::LibLoadingError(culprit, error) => {
                Self::LibLoading(culprit, error)
            }
        }
    }
}

#[derive(Debug)]
pub(crate) enum ArgCountMismatchKind {
    Function,
    Struct,
}

impl std::fmt::Display for FfiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl Error for FfiError {}

impl Machine {
    /// register a struct to be usable with the prolog ffi module
    pub fn register_struct<T: CustomFfiStruct>(&mut self) -> Result<(), FfiSetupError> {
        let fields = T::fields(self);

        unsafe {
            self.register_struct_unchecked(T::type_name(), fields)
        }
    }

    /// register a struct to be usable with the prolog ffi module
    ///
    /// ## Safety
    /// - name must not be unique under all registered types
    /// - the fields must be of the correct type and in the correct order (matching the C struct this is supposed to match)
    pub unsafe fn register_struct_unchecked(&mut self, name: &str, fields: Vec<FfiType>) -> Result<(), FfiSetupError> {

        let struct_type = libffi::middle::Type::structure(
            fields
                .iter()
                .map(|field| field.to_type(&self.foreign_function_table.structs))
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

        let name = AtomTable::build_with(&self.machine_st.atom_tbl, name);

        self.foreign_function_table.structs.try_reserve(1)?;
        self.foreign_function_table.structs.insert(
            name,
            StructImpl {
                ffi_type: struct_type,
                fields,
            },
        );

        Ok(())
    }

    /// register a function to be callable from prolog as ffi:'name'(Args..., Ret) see prolog ffi module for details
    ///
    /// ## Safety
    /// - each name may only be registered once
    pub unsafe fn register_function<F: FfiFn>(
        &mut self,
        name: &str,
        f: F,
    ) -> Result<(), FfiSetupError> {
        let fn_type = f.fn_type(self);

        self.register_function_unchecked(name, f.fn_ptr(), fn_type)
    }

    /// register a function to be callable from prolog as ffi:'name'(Args..., Ret) see prolog ffi module for details
    ///
    /// # Safety
    /// - each name may only be registered once
    /// - fn_ptr must be a pointer to an extern "C" fn with the argument and return type matching the definition in fn_type
    pub unsafe fn register_function_unchecked(&mut self, name: &str, fn_ptr: *mut c_void, fn_type: FnType) -> Result<(), FfiSetupError> {
        let name = AtomTable::build_with(&self.machine_st.atom_tbl, name);

        self.foreign_function_table
            .define_function(name, fn_ptr, &fn_type)?;

        // using if false rather than commenting out or #[cfg(any())] so that the compiler still checks it for correctnes
        if false {
            // FIXME define the function also on the prolog site the following doesn't appear to work

            let inputs = sized_iter_to_heap_list(
                &mut self.machine_st.heap,
                fn_type.args.len(),
                fn_type.args.iter().map(|&arg| atom_as_cell!(arg.to_atom())),
            )
            .map_err(|_| FfiSetupError::AllocationFailed)?;

            let def = functor!(name, [cell(inputs), atom_as_cell((fn_type.ret.to_atom()))]);
            let cell = Heap::functor_writer(def)(&mut self.machine_st.heap)
                .map_err(|_| FfiSetupError::AllocationFailed)?;
            self.machine_st.registers[1] = cell;

            self.run_module_predicate(atom!("ffi"), (atom!("assert_predicate"), 1));
        }

        Ok(())
    }
}

/// make a type registerable with `Machine::register_struct`
///
/// ## Safety
/// - the string returned by type_name must be unique betweem all registered structs and must not shadow a build-in type
/// - the fields must be of the correct type and in the correct order
/// - the struct this represents must be compatible with repr(C)
pub unsafe trait CustomFfiStruct {
    /// the name of the struct as it will be refered to by the prolog machine
    fn type_name() -> &'static str;
    /// the declared fields of the struct in order of declaration
    fn fields(machine: &mut Machine) -> Vec<FfiType>;
}

/// Mark types that can be used for ffi
pub trait FfiTypeable {
    /// The FfiType this type corresponds to
    fn to_type(machine: &mut Machine) -> FfiType;
}

impl<T> FfiTypeable for *mut T {
    fn to_type(_machine: &mut Machine) -> FfiType {
        FfiType::Ptr
    }
}

impl<T> FfiTypeable for *const T {
    fn to_type(_machine: &mut Machine) -> FfiType {
        FfiType::Ptr
    }
}

impl<T> FfiTypeable for Option<&mut T> {
    fn to_type(_machine: &mut Machine) -> FfiType {
        FfiType::Ptr
    }
}

impl<T> FfiTypeable for Option<&T> {
    fn to_type(_machine: &mut Machine) -> FfiType {
        FfiType::Ptr
    }
}

impl FfiTypeable for () {
    fn to_type(_machine: &mut Machine) -> FfiType {
        FfiType::Void
    }
}

impl FfiTypeable for bool {
    fn to_type(_machine: &mut Machine) -> FfiType {
        FfiType::Bool
    }
}

impl<T: FfiTypeable, const N : usize> FfiTypeable for [T; N] {
    fn to_type(machine: &mut Machine) -> FfiType {
        let var = "At";
        let element_type = T::to_type(machine);

        let mut state = machine.run_query2(crate::Term::Compound(String::from(":"), vec![
            Term::Atom(String::from("ffi")),
            Term::Compound(String::from("array_type"), vec![
                Term::Atom(element_type.to_atom().as_str().to_owned()),
                Term::Integer(N.into()),
                Term::Var(String::from(var))
            ])
        ]));

        let result = state.next().expect("Querry should have a result").expect("Querry should succeed");
        assert!(state.next().is_none_or(|answer| matches!(answer, Ok(LeafAnswer::False))));
        drop(state);
        match result {
            crate::LeafAnswer::True => unreachable!("Querry should have bindings"),
            crate::LeafAnswer::False => unreachable!("Querry shouldn't fail"),
            crate::LeafAnswer::Exception(term) => unreachable!("Querry shouldn't throw: {term:?}"),
            crate::LeafAnswer::LeafAnswer { bindings } => {
                let res = bindings.get(var).unwrap_or_else(|| panic!("Querry should have a binding for variable {var}"));
                match res {
                    crate::Term::Atom(atom) => {
                        let array_type = AtomTable::build_with(&machine.machine_st.atom_tbl, atom);
                        FfiType::Struct(array_type)
                    },
                    _ => {
                        unreachable!("Variable {var} should be bound to an atom: {res:?}")
                    }
                }
            },
        }
    }
}

// cannot implement FfiTypeable for &T and &mut T as that conflicts with the impl below

impl<T: CustomFfiStruct> FfiTypeable for T {
    fn to_type(machine: &mut Machine) -> FfiType {
        FfiType::Struct(AtomTable::build_with(
            &machine.machine_st.atom_tbl,
            T::type_name(),
        ))
    }
}

/// Marks functions that may be called from prolog via the ffi interface
#[expect(private_bounds)]
pub trait FfiFn: FfiFnImpl {}
impl<T: FfiFnImpl> FfiFn for T {}

trait FfiFnImpl {
    fn fn_type(&self, machine: &mut Machine) -> FnType;
    fn fn_ptr(&self) -> *mut c_void;
}

macro_rules! impl_ffi_fn {
    ($arg0:ident $(, $arg:ident)*) => {
        impl_ffi_fn!($($arg),*);

        impl<$arg0:FfiTypeable $(, $arg: FfiTypeable)*, R: FfiTypeable> FfiFnImpl for extern "C" fn($arg0 $(, $arg)*) -> R {
            fn fn_type(&self, machine: &mut Machine) -> FnType {
                let args = vec![$arg0::to_type(machine) $(, $arg::to_type(machine))* ];
                let ret = R::to_type(machine);
                FnType {
                    calling_convention: FfiCallingConvention::Default,
                    args,
                    ret,
                }
            }

            fn fn_ptr(&self) -> *mut c_void {
                *self as *mut c_void
            }
        }
    };
    () => {}
}

// implement FfiFnImpl for exteren "C" functions with 1 to 16 arguments
impl_ffi_fn!(A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15);

// implement FfiFnImpl for exteren "C" functions with 0 arguments
impl<R: FfiTypeable> FfiFnImpl for extern "C" fn() -> R {
    fn fn_type(&self, machine: &mut Machine) -> FnType {
        FnType {
            calling_convention: FfiCallingConvention::Default,
            args: vec![],
            ret: R::to_type(machine),
        }
    }

    fn fn_ptr(&self) -> *mut c_void {
        *self as *mut c_void
    }
}
