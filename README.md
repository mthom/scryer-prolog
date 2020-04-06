# Scryer Prolog

Scryer Prolog aims to become to ISO Prolog what GHC is to Haskell: an open
source industrial strength production environment that is also a
testbed for bleeding edge research in logic and constraint
programming, which is itself written in a high-level language.

## Phase 1

Produce an implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf).

Phase 1 has been completed in that Scryer Prolog implements in some form
all of the WAM book, including lists, cuts, Debray allocation, first
argument indexing, last call optimization and conjunctive queries.

## Phase 2

Extend Scryer Prolog to include the following, among other features:

- [x] call/N as a built-in meta-predicate.
- [x] ISO Prolog compliant throw/catch.
- [x] Built-in and user-defined operators of all fixities, with custom
      associativity and precedence.
- [x] Bignum, rational number and floating point arithmetic.
- [x] Built-in control operators (`,`, `;`, `->`, etc.).
- [x] A revised, not-terrible module system.
- [x] Built-in predicates for list processing and top-level declarative
      control (`setup_call_cleanup/3`, `call_with_inference_limit/3`,
      etc.)
- [x] ~~Default representation of strings as lists of characters, using a packed
      internal representation.~~
- [x] `term_expansion/2` and `goal_expansion/2`.
- [x] Definite Clause Grammars.
- [x] Attributed variables using the SICStus Prolog interface and
      semantics. Adding coroutines like `dif/2`, `freeze/2`, etc.
      is straightforward with attributed variables.
  - [x] Support for `verify_attributes/3`
  - [x] Support for `attribute_goals/2` and `project_attributes/2`
  - [x] `call_residue_vars/2`
- [x] `if_` and related predicates, following the developments of the
      paper "Indexing `dif/2`".
- [x] All-solutions predicates (`findall/{3,4}`, `bagof/3`, `setof/3`, `forall/2`).
- [x] Clause creation and destruction (`asserta/1`, `assertz/1`,
      `retract/1`, `abolish/1`) with logical update semantics.
- [x] Backtrackable and non-backtrackable global variables via `bb_get/2`
      `bb_put/2` (non-backtrackable) and `bb_b_put/2`
      (backtrackable).
- [x] Delimited continuations based on reset/3, shift/1 (documented in
      "Delimited Continuations for Prolog").
- [x] Tabling library based on delimited continuations
      (documented in "Tabling as a Library with Delimited Control").
- [x] A _redone_ representation of strings as difference lists of
      characters, using a packed internal representation.
- [x] clp(B) and clp(ℤ) as builtin libraries.
- [ ] Streams and predicates for stream control (_in progress_).
- [ ] A compacting garbage collector satisfying the five
      properties of "Precise Garbage Collection in Prolog."
- [ ] Mode declarations.

## Phase 3

Use the WAM code produced by the completed code generator to get
JIT-compiled and -executed Prolog programs. The question of how to get
assembly from WAM code is something I'm still considering.

It's my hope to use Scryer Prolog as the logic engine of a low level (and
ideally, very fast) [Shen](http://shenlanguage.org) implementation.

## Nice to have features

There are no current plans to implement any of these, but they might be
nice to have in the future. They'd make a good project for anyone wanting
to contribute code to Scryer Prolog.

1. Implement the global analysis techniques described in Peter van
Roy's thesis, "Can Logic Programming Execute as Fast as Imperative
Programming?"

2. Add unum representation and arithmetic, using either an existing
unum implementation or an ad hoc one. Unums are described in
Gustafson's book "The End of Error."

3. Add concurrent tables to manage shared references to atoms and
strings.

4. Add some form of JIT predicate indexing.

## Installing Scryer Prolog

First, install the latest stable version of
[Rust](https://www.rust-lang.org/en-US/install.html) using your
preferred method. Scryer tends to use features from newer Rust
releases, whereas Rust packages in Linux distributions, Macports,
etc. tend to lag behind. [rustup](http://rustup.rs) will keep your
Rust updated to the latest stable release; any existing Rust
distribution should be uninstalled from your system before rustup is
used.

Scryer Prolog can be installed with cargo, like so:

```
$> cargo install scryer-prolog
```

cargo will download and install the libraries Scryer Prolog uses
automatically from crates.io. You can find the `scryer-prolog`
executable in `~/.cargo/bin`.

Publishing Rust crates to crates.io and pushing to git are entirely
distinct, independent processes, so to be sure you have the latest
commit, it is recommended to clone directly from this git repository,
which can be done as follows:

```
$> git clone https://github.com/mthom/scryer-prolog
$> cd scryer-prolog
$> cargo run [--release]
```

The optional `--release` flag will perform various optimizations,
producing a faster executable.

## Tutorial
To enter a multi-clause predicate, the directive "[user]" is used.

For example,
```
?- [user].
(type Enter + Ctrl-D to terminate the stream when finished)
p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
p(X, Y, Z) :- h(Y), z(Z).
?- [user].
(type Enter + Ctrl-D to terminate the stream when finished)
h(x). h(y).
h(z).
```
In the example, `Enter + Ctrl-D` is used to terminate the standard
input stream. The instructive message is always printed.

Queries are issued as
```
?- p(X, Y, Z).
```

Pressing `SPACE` will backtrack through other possible answers, if any exist.
Pressing `.` will abort the search and return to the prompt.

Wildcards work as well:

```
?- [user].
(type Enter + Ctrl-D to terminate the stream when finished)
member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).
?- member(X, [a, b, c]).
   X = a
;  X = b
;  X = c
;  false.
```
and so do conjunctive queries:
```
?- [user].
(type Enter + Ctrl-D to terminate the stream when finished)
f(X) :- g(X).
g(x). g(y). g(z).
h(call(f, X)).
?- h(X), X.
   X = call(f,x)
;  X = call(f,y)
;  X = call(f,z).
```

Note that the values of variables belonging to successful queries are
printed out, on one line each. Uninstantiated variables are denoted by
a number preceded by an underscore (`X = _0` in an example above).

To quit scryer-prolog, type
```
?- halt.
```

### Dynamic operators

Scryer supports dynamic operators. Using the built-in
arithmetic operators with the usual precedences,

```
?- write_canonical(-5 + 3 - (2 * 4) // 8), nl.
   -(+(-5,3),//(*(2,4),8))
true.
```

New operators can be defined using the `op` declaration.

### Partial strings

Scryer has three specialized non-ISO predicates for handling so-called
"partial strings." Partial strings imitate difference lists of
characters, but their characters are packed in UTF-8 format, a much
more efficient alternative to how lists of characters are represented
in many other Prologs.

To use partial strings, the `iso_ext` library must be loaded:

`?- use_module(library(iso_ext)).`

If `X` is a free variable, the query

`?- partial_string("abc", X, _), X = [a, b, c | Y], partial_string(X),
partial_string_tail(X, Tail), Tail == Y.`

will succeed, posting:

`Tail = Y, X = [a,b,c|Y].`

By all appearances, partial strings are plain Prolog lists.

### Modules

Scryer has a simple predicate-based module system. It provides a
way to separate units of code into distinct namespaces, for both
predicates and operators. See the files
[`src/prolog/lib/*.pl`](src/prolog/lib) for
examples.

At the time of this writing, many predicates reside in their own
modules that need to be imported before they can be used.
The modules that ship with Scryer&nbsp;Prolog are also called
*library*&nbsp;modules or *libraries*, and include:

* [`lists`](src/prolog/lib/lists.pl)
  providing `length/2`, `member/2`, `select/3`, `append/[2,3]`,
  `foldl/[4,5]`, `maplist/[2-9]`, `same_length/2`, `transpose/2` etc.
* [`dcgs`](src/prolog/lib/dcgs.pl)
  Definite Clause Grammars (DCGs), a built-in grammar mechanism
  that uses the operator `(-->)/2` to define grammar rules,
  and the predicates `phrase/[2,3]` to invoke them.
* [`dif`](src/prolog/lib/dif.pl)
  The predicate `dif/2` provides declarative disequality:
  It is true if and only if its arguments are different, and
  delays the test until a sound decision can be made.
* [`reif`](src/prolog/lib/reif.pl)
  providing `if_/3`, `tfilter/3` and related predicates
  as described in *Indexing&nbsp;dif/2*.
* [`clpz`](src/prolog/lib/clpz.pl)
  CLP(ℤ): Constraint Logic Programming over Integers,
  providing declarative integer arithmetic via `(#=)/2`, `(#\=)/2`,
  `(#>=)/2` etc., and various global constraints and
  enumeration predicates for solving combinatorial tasks.
* [`pairs`](src/prolog/lib/pairs.pl)
  By convention, *pairs* are Prolog terms with
  principal&nbsp;functor `(-)/2`, written as `Key-Value`.
  This library provides `pairs_keys_values/3`,
  `pairs_keys/2`, and other predicates to reason about pairs.
* [`si`](src/prolog/lib/si.pl)
  The predicates `atom_si/1`, `integer_si/1`, `atomic_si/1`
  and `list_si/1` implement sound type checks. They raise
  instantiation errors if no decision can be made.
  They are declarative replacements for logically flawed
  lower-level type tests. For instance, instead of `integer(X)`,
  write `integer_si(X)` to ensure soundness of your programs.
  "si" stands for *sufficiently instantiated*, and also for
  *sound&nbsp;inference*.
* [`error`](src/prolog/lib/error.pl)
  `must_be/2` and `can_be/2` complement the type checks provided
  by `library(si)`, and are especially useful for Prolog library
  authors.
* [`tabling`](src/prolog/lib/tabling.pl)
  The operator `(table)/1` is used in directives that prepare
  predicates for tabled execution (SLG&nbsp;resolution).
* [`format`](src/prolog/lib/format.pl)
  The nonterminal `format_//2` is used to describe formatted output,
  arranging arguments according to a given format&nbsp;string.
  The predicate `format/2` is provided for impure output.
* [`assoc`](src/prolog/lib/assoc.pl)
  providing `empty_assoc/1`, `get_assoc/3`, `put_assoc/4` etc.
  to manage elements in AVL&nbsp;trees which ensure
  *O*(log(*N*))&nbsp;access.
* [`clpb`](src/prolog/lib/clpb.pl)
  CLP(B): Constraint Logic Programming over Boolean variables,
  a BDD-based SAT&nbsp;solver provided via the predicates
  `sat/1`, `taut/2`, `labeling/1` etc.

To use predicates provided by the `lists` library, write:

```
?- use_module(library(lists)).
```

To load modules contained in files, the `library` functor can be
omitted, prompting Scryer to search for the file (specified as an
atom) from its working directory:

```
?- use_module('file.pl').
```

`use_module` directives can be qualified by adding a list of imports:

```
?- use_module(library(lists), [member/2]).
```

A qualified `use_module` can be used to remove imports from the
toplevel by calling it with an empty import list.

The `(:)/2` operator resolves calls to predicates that might not be
imported to the current working namespace:

```
?- lists:member(X, Xs).
```

The [user] prompt can also be used to define modules inline at the
REPL:

```
?- [user].
(type Enter + Ctrl-D to terminate the stream when finished)
:- module(test, [local_member/2]).
:- use_module(library(lists)).

local_member(X, Xs) :- member(X, Xs).
```

The user listing can also be terminated by placing `end_of_file.` at
the end of the stream.
