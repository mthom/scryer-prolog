:- module(ffi, [use_foreign_module/2, foreign_struct/2, with_locals/2, allocate/4, deallocate/3, read_ptr/3, array_type/3]).

/** Foreign Function Interface

This module contains predicates used to call native code (exposed by the C ABI).
It uses [libffi](https://sourceware.org/libffi/) under the hood. The bridge is very simple
and is very unsafe and should be used with care. FFI isn't the only way to communicate with
the outside world in Prolog: sockets, pipes and HTTP may be good enough for your use case.

The main predicate is `use_foreign_module/2`. It takes a library name (which depending on the
operating system could be a `.so`, `.dylib` or `.dll` file). and a list of functions. Each
function is defined by its name, a list of the type of the arguments, and the return argument.

Types available are: `sint8`/`i8`, `uint8`/`u8`, `sint16`/`i16`, `uint16`/`u16`, `sint32`/`i32`, `uint32`/`u32`, `sint64`/`i64`,
`uint64`/`u64`, `f32`, `f64`, `cstr`, `void`, `bool`, `ptr` and custom structs, which can be defined
with `foreign_struct/2`.

After that, each function on the lists maps to a predicate created in the ffi module which
are used to call the native code.
The predicate takes the functor name after the function name. Then, the arguments are the input
arguments followed by a return argument. However, functions with return type `void` or `bool`
don't have that return argument. Predicates with `void` always succeed and `bool` predicates depend
on the return value on the native side.

```
ffi:FUNCTION_NAME(+InputArg1, ..., +InputArgN, -ReturnArg). % for all return types except void and bool
ffi:FUNCTION_NAME(+InputArg1, ..., +InputArgN). % for void and bool
```

## Notes regarding cstr

- When using `cstr` as an argument type the string will be deallocated once the function returns.
- When using `cstr` as a return type the string will be copied and won't be deallocated.


## Example

For example, let's see how to define a function from the [raylib](https://www.raylib.com/) library.

```
?- use_foreign_module("./libraylib.so", ['InitWindow'([sint32, sint32, cstr], void)]).
```

This creates a `'InitWindow'` predicate under the ffi module. Now, we can call it:

```
?- ffi:'InitWindow'(800, 600, "Scryer Prolog + Raylib").
```

And a new window should pop up!
*/

:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).

%% foreign_struct(+Name, +Elements).
%
% Defines a new struct type with name Name, composed of the elements Elements, which is a list
% of other types.
%
% The name of the types doesn't matter, but the order of Elements must match the ones in the
% native code.
%
% Example:
%
% ```
% ?- foreign_struct(color, [uint8, uint8, uint8, uint8]).
% ```
foreign_struct(Name, Elements) :-
    '$define_foreign_struct'(Name, Elements).


%% use_foreign_module(+LibName, +Predicates)
%
% - LibName the path to the shared library to load/bind
% - Predicates list of function definitions
%
%   Each function definition is a functor of arity 2.
%   The functor name is the name of the function to bind,
%   the first argument is the list of arguments of the function,
%   the second argument is the return type of the function.
%
%   This will define a predicate in the ffi module with the defined name,
%   for void and bool return type functions the arity will match the length of the arguments list,
%   for other return types there will be an additional out parameter.
%
use_foreign_module(LibName, Predicates) :-
    '$load_foreign_lib'(LibName, Predicates),
    maplist(assert_predicate, Predicates).

assert_predicate(PredicateDefinition) :-
    PredicateDefinition =.. [Name, Inputs, void],
    length(Inputs, NumInputs),
    functor(Head, Name, NumInputs),
    term_variables(Head, TermList),
    Body = (
	'$foreign_call'(Name, TermList, _),!
    ),
    Predicate = (Head:-Body),
    assertz(ffi:Predicate).

assert_predicate(PredicateDefinition) :-
    PredicateDefinition =.. [Name, Inputs, bool],
    length(Inputs, NumInputs),
    functor(Head, Name, NumInputs),
    term_variables(Head, TermList),
    Body = (
	'$foreign_call'(Name, TermList, 1),!
    ),
    Predicate = (Head:-Body),
    assertz(ffi:Predicate).

assert_predicate(PredicateDefinition) :-
    PredicateDefinition =.. [Name, Inputs, Return],
    \+ member(Return, [void, bool]),
    length(Inputs, NumInputs),
    NumArgs is NumInputs + 1,
    functor(Head, Name, NumArgs),
    term_variables(Head, TermList),
    Body = (
	lists:append(TermListInputs, [TermListReturn], TermList),
	'$foreign_call'(Name, TermListInputs, TermListReturn),!
    ),
    Predicate = (Head:-Body),
    assertz(ffi:Predicate).

%% allocate(+Allocator, +Type, +Args, -Ptr)
%
% Using the Allocator allocate Type initialized with Args and 
% unify Ptr with a pointer to that allocation.
%
allocate(Allocator, Type, Args, Ptr) :-
    must_be(var, Ptr),
    must_be(atom, Type),
    must_be(atom, Allocator),
    '$ffi_allocate'(Allocator, Type, Args, Ptr).


%% read_ptr(+Type, +Ptr, -Value)
%
% Read a value of Type from the pointer Ptr and unify the read value with Value
%
% For type cstr take read a nul-terminated utf-8 string starting at Ptr.
%
read_ptr(Type, Ptr, Value) :-
    must_be(atom, Type),
    must_be(integer, Ptr),
    '$ffi_read_ptr'(Type, Ptr, Value).

%% deallocate(+Allocator, +Type, +Ptr)
%
% Deallocate the allocation at Ptr of Type allocated with Allocator
%
deallocate(Allocator, Type, Ptr) :-
    must_be(atom, Allocator),
    must_be(integer, Ptr),
    '$ffi_deallocate'(Allocator, Type, Ptr).

:- dynamic(is_array_type_defined/1).

%% array_type(+ElemType, +Len, -ArrayType)
%
% unify the ffi type for an array of lenth Len with element type ElemType with ArrayType
%
array_type(ElemType, Len, ArrayType) :-
    (Len =< 0 -> domain_error(greater_than_zero, Len, array_type/3); true),
    phrase(format_("$[~a;~d]", [ElemType, Len]), ArrayTypeName),
    atom_chars(ArrayType, ArrayTypeName),
    (is_array_type_defined(ArrayType) -> true
    ;   length(Fields, Len),
        maplist(=(ElemType), Fields),
        foreign_struct(ArrayType, Fields),
        assertz(is_array_type_defined(ArrayType))
    ).

:- meta_predicate(with_locals(?, 0)).

%% with_locals(+Locals, :Goal)
%
%  Allocate the Locals, evaluate the Goal and deallocate the Locals.
%  The Locals will also be cleandup when Goal fails or throws an error.
%
%  Locals is a list of local variable definitions let(-Ptr, +Type, +Args).
%  Ptr will be unified with the pointer to the local of Type initialized with Args.
%
with_locals(Locals, Goal) :-
    verify_locals(Locals),
    setup_call_cleanup(
        allocate_locals(Locals),
        Goal,
        deallocate_locals(Locals)
    ).

verify_locals(Locals) :-
    must_be(list, Locals),
    ( maplist(verify_local, Locals) -> true
    ; domain_error(locals_decl_list, Locals, [verify_locals/1])
    ).

verify_local(let(Var, Type, Init)) :-
    must_be(var, Var),
    must_be(atom, Type),
    ground(Init).

allocate_locals([]).
allocate_locals([let(Var, Type, Init) | Ls]) :-
    allocate(rust, Type, Init , Var),
    (catch(allocate_locals(Ls), E, (deallocate_locals([let(Var, Type, Init)]), throw(E))) -> true
    ; deallocate_locals([let(Var, Type, Init)]), false
    ).

deallocate_locals([]).
deallocate_locals([let(Var, Type, _) | Ls]) :-
    deallocate(rust, Type, Var),
    deallocate_locals(Ls).
