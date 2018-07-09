# rusty-wam

rusty-wam aims to become to ISO Prolog what GHC is to Haskell: an open
source industrial strength production environment that is also a
testbed for bleeding edge research in logic and constraint
programming, which is itself written in a high-level language.

## Phase 1

Produce an implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf).

Phase 1 has been completed in that rusty-wam implements in some form
all of the WAM book, including lists, cuts, Debray allocation, first
argument indexing, last call optimization and conjunctive queries.

## Phase 2

Extend rusty-wam to include the following, among other features:

* call/N as a built-in meta-predicate (_done_).
* ISO Prolog compliant throw/catch (_done_).
* Built-in and user-defined operators of all fixities, with custom
  associativity and precedence (_done_).
* Bignum, rational number and floating point arithmetic (_done_).
* Built-in control operators (`,`, `;`, `->`, etc.) (_done_).
* A revised, not-terrible module system (_in progress_).
* Built-in predicates for list processing and top-level declarative
  control (`setup_call_control/3`, `call_with_inference_limit/3`,
  etc.) (NEEDS REVISION)
* Definite Clause Grammars
* Attributed variables using the SICStus Prolog interface and
  semantics. Adding coroutines like `dif/2`, `freeze/2`, etc.
  is straightforward with attributed variables.
* An occurs check.
* Mode declarations.
* Extensions for clp(FD).
* `if_` and related predicates, following the developments of the
  paper "Indexing `dif/2`".
* Strings, blobs, and other data types.

## Phase 3

Use the WAM code produced by the completed code generator to get
JIT-compiled and -executed Prolog programs. The question of how to get
assembly from WAM code is something I'm still considering.

It's my hope to use rusty-wam as the logic engine of a low level (and
ideally, very fast) [Shen](http://shenlanguage.org) implementation.

## Nice to have features

There are no current plans to implement any of these, but they might be
nice to have in the future. They'd make a good project for anyone wanting
to contribute code to rusty-wam.

1. Implement the global analysis techniques described in Peter van
Roy's thesis, "Can Logic Programming Execute as Fast as Imperative
Programming?"

2. Add unum representation and arithmetic, using either an existing
unum implementation or an ad hoc one. Unums are described in
Gustafson's book "The End of Error."

3. Add support for shift/reset delimited continuations, see "Delimited
Continuations for Prolog."

4. Add an incremental compacting garbage collector for the heap.

5. Add concurrent tables to manage shared references to atoms and
strings.

6. Add optional SLG resolution for fast memoization of predicates.

7. Add some form of JIT predicate indexing.

## Installing rusty-wam

First, install the latest stable version of
[Rust](https://www.rust-lang.org/en-US/install.html) using your
preferred method. Then clone the rusty-wam repo and build it with
cargo, like so:

```
$> git clone https://github.com/mthom/rusty-wam --recursive
$> cd rusty-wam
$> cargo build
```

cargo will download and install the libraries rusty-wam uses
automatically.  rusty-wam can be run with the command `cargo run`, and
likewise tests can be run with `cargo test`.

Note on compatibility: rusty-wam should work on Linux, Mac OS X, and
FreeBSD. Windows support hinges on the Termion library working in
Windows terminals, which isn't yet the case, although work is
underway. See the relevant Termion
[issue](https://github.com/ticki/termion/issues/103) for more
information.

## Built-in predicates

The following predicates are built-in to rusty-wam.

* Arithmetic support:
    * `is/2` works for `(+)/2`, `(-)/{1,2}`, `(*)/2`, `(//)/2`, `(div)/2`, `(/)/2`, `(rdiv)/2`,
      `(xor)/2`, `(rem)/2`, `(mod)/2`, `(/\)/2`, `(\/)/2`, `(>>)/2`, `(<<)/2`.
    * Comparison operators: `>`, `<`, `=<`, `>=`, `=:=`, `=\=`.
* `(:)/2`
* `(@>)/2`
* `(@>=)/2`
* `(@=<)/2`
* `(@<)/2`
* `(=@=)/2`
* `(\=@=)/2`
* `(\+)/1`
* `(==)/2`
* `(\==)/2`
* `(=)/2`
* `(\=)/2`
* `(=..)/2`
* `(->)/2`
* `(;)/2`
* `acyclic_term/2`
* `append/3`
* `arg/3`
* `atom/1`
* `atomic/1`
* `between/3`
* `call/1..62`
* `catch/3`
* `compare/3`
* `compound/1`
* `cyclic_term/1`
* `display/1`
* `duplicate_term/2`
* `false/0`
* `float/1`
* `functor/3`
* `ground/1`
* `integer/1`
* `is_list/1`
* `keysort/2`
* `length/2`
* `maplist/2..9`
* `member/2`
* `memberchk/2`
* `nonvar/1`
* `once/1`
* `rational/1`
* `repeat/0`
* `reverse/2`
* `select/3`
* `sort/2`
* `string/1`
* `throw/1`
* `true/0`
* `var/1`

## Tutorial
To enter a multi-clause predicate, the brackets ":{" and "}:" are used
as delimiters. They must be contained entirely within their own lines.

For example,
```
prolog> :{
p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
p(X, Y, Z) :- h(Y), z(Z).
}:
prolog> :{
h(x).
h(y).
h(z).
}:
```

Single clause predicates can be entered without brackets, as in
```
prolog> p(X) :- q(X).
prolog> f(s).
prolog> z(Z).
```

Queries are issued as
```
prolog> ?- p(X, Y, Z).
```

Given the above work, the result of the query will be
```
prolog> ?- p(X, Y, Z).
true
Y = x
X = _0
Z = _2
```

Pressing `SPACE` will backtrack through other possible answers, if any exist.
Pressing `.` will abort the search and return to the prompt.

Wildcards work as well:

```
prolog> :{
member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).
}:
prolog> ?- member(X, [a, b, c]).
true .
X = a ;
X = b ;
X = c ;
false.
```
and so do conjunctive queries:
```
prolog> f(X) :- g(X).
prolog> g(x). g(y). g(z).
prolog> h(call(f, X)).
prolog> ?- h(X), X.
true .
X = call(f, x) ;
X = call(f, y) ;
X = call(f, z).
```

Note that the values of variables belonging to successful queries are
printed out, on one line each. Uninstantiated variables are denoted by
a number preceded by an underscore (`X = _0` in an example above).

### Dynamic operators

rusty-wam supports dynamic operators. Using the built-in
arithmetic operators with the usual precedences,

```
prolog> ?- display(-5 + 3 - (2 * 4) // 8).
'-'('+'('-'(5), 3), '//'('*'(2, 4), 8))
true.
```

New operators can be defined using the `op` declaration.

### Modules

rusty-wam has a simple predicate-based module system. It provides a
way to separate units of code into distinct namespaces, for both
predicates and operators. See the files `src/prolog/lib/*.pl` for
examples.

At the time of this writing, several control and list processing
operators and predicates are hidden in their own modules that have not
been exported to the toplevel. To export them, write

```
prolog> :- use_module(library(lists)).
prolog> :- use_module(library(control)).
```

To define modules inline at the REPL, use the ":{{" and "}}:"
delimiters:

```
prolog> :{{
:- module(test, [local_member/2]).
:- use_module(library(lists)).

local_member(X, Xs) :- member(X, Xs).
}}:
```

`use_module` directives can be qualified by adding a list of imports:

```
prolog> :- use_module(library(lists), [member/2]).
```

A qualified `use_module` can be used to remove imports from the
toplevel by calling it with an empty import list.

The `(:)/2` operator resolves calls to predicates that might not be
imported to the current working namespace:

```
prolog> ?- lists:member(X, Xs).
```
