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
* A revised, not-terrible module system (_done, I think_).
* Built-in predicates for list processing and top-level declarative
  control (`setup_call_cleanup/3`, `call_with_inference_limit/3`,
  etc.) (_done_)
* Default representation of strings as list of chars, using a packed
  internal representation (_done_).
    - A representation of 'partial strings' as difference lists
      of characters (_done_).
* `term_expansion/2` and `goal_expansion/2` (_done_).
* Definite Clause Grammars (_done_).
* Attributed variables using the SICStus Prolog interface and
  semantics. Adding coroutines like `dif/2`, `freeze/2`, etc.
  is straightforward with attributed variables (_done_).
     - [x] Support for `verify_attributes/3`
     - [x] Support for `attribute_goals/2` and `project_attributes/2`
     - [x] `call_residue_vars/2`
* `if_` and related predicates, following the developments of the
  paper "Indexing `dif/2`" (_done_).
* All-solutions predicates (`findall/{3,4}`, `bagof/3`, `setof/3`) (_done_).
* Clause creation and destruction (`asserta/1`, `assertz/1`,
  `retract/1`, `abolish/1`) with logical update semantics (_in progress_).
* Streams and predicates for stream control.
* An incremental compacting garbage collector satisfying the five
  properties of "Precise Garbage Collection in Prolog."
* Mode declarations.
* Extensions for clp(FD).

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

4. Add concurrent tables to manage shared references to atoms and
strings.

5. Add optional SLG resolution for fast memoization of predicates.

6. Add some form of JIT predicate indexing.

## Installing rusty-wam

First, install the latest stable version of
[Rust](https://www.rust-lang.org/en-US/install.html) using your
preferred method. Then install the latest rusty-wam with cargo,
like so:

```
$> cargo install rusty-wam
```

cargo will download and install the libraries rusty-wam uses
automatically. You can find the `rusty-wam` executable in
`~/.cargo/bin`.

Note on compatibility: rusty-wam should work on Linux, Mac OS X, and
FreeBSD. Windows support hinges on the Termion library working in
Windows terminals, which isn't yet the case, although work is
underway. See the relevant Termion
[issue](https://github.com/ticki/termion/issues/103) for more
information.

## Built-in predicates

The following predicates are built-in to rusty-wam.

* Arithmetic support:
    * `is/2` works for `(+)/2`, `(-)/{1,2}`, `(*)/2`, `(//)/2`, `(**)/2`, `(div)/2`, `(/)/2`, `(rdiv)/2`,
      `(xor)/2`, `(rem)/2`, `(mod)/2`, `(/\)/2`, `(\/)/2`, `(>>)/2`, `(<<)/2`, `abs/1`.
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
* `asserta/1`
* `assertz/1`
* `atom/1`
* `atomic/1`
* `bagof/3`
* `between/3`
* `call/1..62`
* `call_cleanup/2`
* `call_with_inference_limit/3`
* `call_residue_vars/2`
* `can_be/2`
* `catch/3`
* `clause/2`
* `compare/3`
* `compound/1`
* `copy_term/2`
* `cyclic_term/1`
* `dif/2`
* `expand_goal/2`
* `expand_term/2`
* `false/0`
* `findall/{3,4}`
* `float/1`
* `freeze/2`
* `functor/3`
* `gen_int/1`
* `gen_nat/1`
* `goal_expansion/2`
* `ground/1`
* `integer/1`
* `is_list/1`
* `is_partial_string/1`
* `keysort/2`
* `length/2`
* `maplist/2..9`
* `member/2`
* `memberchk/2`
* `must_be/2`
* `nl/0`
* `nonvar/1`
* `numbervars/2`
* `numlist/{2,3}`
* `once/1`
* `partial_string/2`
* `phrase/{2,3}`
* `rational/1`
* `read/1`
* `repeat/{0,1}`
* `reverse/2`
* `select/3`
* `setof/3`
* `setup_call_cleanup/3`
* `sort/2`
* `string/1`
* `term_expansion/2`
* `term_variables/2`
* `throw/1`
* `true/0`
* `user:goal_expansion/2`
* `user:term_expansion/2`
* `var/1`
* `write/1`
* `write_canonical/1`
* `writeq/1`
* `write_term/2`

## Tutorial
To enter a multi-clause predicate, the directive "[user]" is used.

For example,
```
prolog> [user]
(type Enter + Ctrl-D to terminate the stream when finished)
p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
p(X, Y, Z) :- h(Y), z(Z).
prolog> [user]
(type Enter + Ctrl-D to terminate the stream when finished)
h(x). h(y).
h(z).
```
In the example, `Enter + Ctrl-D` is used to terminate the standard
input stream. The instructive message is always printed.

Queries are issued as
```
prolog> ?- p(X, Y, Z).
```

Pressing `SPACE` will backtrack through other possible answers, if any exist.
Pressing `.` will abort the search and return to the prompt.

Wildcards work as well:

```
prolog> [user]
member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).
prolog> ?- member(X, [a, b, c]).
true .
X = a ;
X = b ;
X = c ;
false.
```
and so do conjunctive queries:
```
prolog> [user]
f(X) :- g(X).
prolog> [user]
g(x). g(y). g(z).
prolog> [user]
h(call(f, X)).
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
prolog> ?- write_canonical(-5 + 3 - (2 * 4) // 8).
-(+(-(5), 3), //(*(2, 4), 8))
true.
```

New operators can be defined using the `op` declaration.

### Partial strings

rusty-wam has two specialized, non-ISO builtin predicates for handling
so-called "partial strings". Partial strings imitate difference lists
of characters, but are much more space efficient. This efficiency
comes at the cost of full generality -- you cannot unify the tail
variables of two distinct partial strings, because their buffers will
always be distinct.

If `X` is a free variable, the query

`?- partial_string("abc", X), X = [a, b, c | Y], is_partial_string(X),
is_partial_string(Y).`

will succeed. Further, if `Y` a free variable, unifying `Y` against
another string, "def" in this case, produces the equations

`X = [a, b, c, d, e, f], Y = [d, e, f].`

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

The [user] prompt can also be used to define modules inline at the
REPL:

```
prolog> [user]
:- module(test, [local_member/2]).
:- use_module(library(lists)).

local_member(X, Xs) :- member(X, Xs).
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
