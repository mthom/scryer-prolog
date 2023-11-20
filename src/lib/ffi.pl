:- module(ffi, [use_foreign_module/2, foreign_struct/2]).

/** Foreign Function Interface

This module contains predicates used to call native code (exposed by the C ABI).
It uses [libffi](https://sourceware.org/libffi/) under the hood. The bridge is very simple
and is very unsafe and should be used with care. FFI isn't the only way to communicate with
the outside world in Prolog: sockets, pipes and HTTP may be good enough for your use case.

The main predicate is `use_foreign_module/2`. It takes a library name (which depending on the
operating system could be a `.so`, `.dylib` or `.dll` file). and a list of functions. Each
function is defined by its name, a list of the type of the arguments, and the return argument.

Types available are: `sint8`, `uint8`, `sint16`, `uint16`, `sint32`, `uint32`, `sint64`,
`uint64`, `f32`, `f64`, `cstr`, `void`, `bool`, `ptr` and custom structs, which can be defined
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
