# Scryer Prolog

Scryer Prolog aims to become to ISO Prolog what GHC is to Haskell: an open
source industrial strength production environment that is also a
testbed for bleeding edge research in logic and constraint
programming, which is itself written in a high-level language.

![Scryer Logo: Cryer](logo/scryer.png)

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
- [x] `if_/3` and related predicates, following the developments of the
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
- [x] Streams and predicates for stream control.
  - [x] A simple sockets library representing TCP connections as streams.  
- [ ] Incremental compilation and loading process, newly written,
      primarily in Prolog. (_in progress_)
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

### Native Install (Unix Only)

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

### Docker Install (All Platforms)

First, install [Docker](https://docs.docker.com/get-docker/) on Linux,
Windows, or Mac.

Once Docker is installed, you can download and run Scryer Prolog with a single
command:
```
$> docker run -it mjt128/scryer-prolog
```

To consult your Prolog files, bind mount your programs folder as a
[Docker volume](https://docs.docker.com/storage/volumes/):

```
$> docker run -v /home/user/prolog:/mnt -it mjt128/scryer-prolog
?- consult('/mnt/program.pl').
true.
```

This works on Windows too:

```
$> docker run -v C:\Users\user\Documents\prolog:/mnt -it mjt128/scryer-prolog
?- consult('/mnt/program.pl').
true.
```

## Tutorial

Prolog files are loaded by specifying them as arguments on the command
line. For example, to load `program.pl`, use:

```
$> scryer-prolog program.pl
```

Loading a Prolog file is also called “consulting” it. The built-in
predicate `consult/1` can be used to consult a file from within
Prolog:

```
?- consult('program.pl').
```

As an abbreviation for `consult/1`, you can specify a *list* of
program files, given as *atoms*:

```
?- ['program.pl'].
```

The special notation `[user]` is used to read Prolog&nbsp;text from
standard input. For example,

```
?- [user].
hello(declarative_world).
hello(pure_world).
```

Pressing `RETURN` followed by `Ctrl-d` stops reading from
standard&nbsp;input and consults the entered Prolog&nbsp;text.

After a program is consulted, you can ask *queries* about the
predicates it defines. For example, with the program shown above:

```
?- hello(What).
   What = declarative_world
;  What = pure_world.
```

Press `SPACE` to show further answers, if any exist. Press `RETURN` or
&nbsp;`.` to abort the search and return to the toplevel&nbsp;prompt.
Press&nbsp;`h` to show a help message.

To quit Scryer Prolog, use the standard predicate `halt/0`:

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

### Strings and partial strings

In Scryer Prolog, the default value of the Prolog flag `double_quotes`
is `chars`, which is also the recommended setting. This means that
double-quoted strings are interpreted as lists of *characters*, in the
tradition of Marseille&nbsp;Prolog.

For example, the following query succeeds:

```
?- "abc" = [a,b,c].
   true.
```

Internally, strings are represented very compactly in packed
UTF-8&nbsp;encoding. A naive representation of strings as lists of
characters would use one memory&nbsp;cell per character, one
memory&nbsp;cell per list constructor, and one memory&nbsp;cell for
each tail that occurs in the list. Since one memory&nbsp;cell takes
8&nbsp;bytes on 64-bit machines, the packed representation used by
Scryer&nbsp;Prolog yields an up&nbsp;to **24-fold&nbsp;reduction** of
memory usage, and corresponding reduction of memory&nbsp;accesses when
creating and processing strings.

Scryer Prolog uses the same efficient encoding for *partial* strings,
which appear to Prolog code as partial lists of characters. The
predicate `partial_string/3` from `library(iso_ext)` lets you
construct partial&nbsp;strings explicitly. For example:

```
?- partial_string("abc", Ls0, Ls).
   Ls0 = [a,b,c|Ls].
```

In this case, and as the answer illustrates, `Ls0` is
indistinguishable from a partial&nbsp;list with tail&nbsp;`Ls`, while
the efficient packed representation is used internally.

An important design goal of Scryer Prolog is to *automatically* use
the efficient string representation whenever possible. Therefore, it
is only very rarely necessary to use `partial_string/3` explicitly. In
the above example, posting <tt>Ls0&nbsp;=&nbsp;[a,b,c|Ls]</tt> yields
the exact same internal representation, and has the advantage that
only the standard predicate&nbsp;`(=)/2` is used.

Definite clause grammars as provided by `library(dcgs)` are ideally
suited for reasoning about strings.

Partial strings were first proposed by Ulrich Neumerkel in issue
[#95](https://github.com/mthom/scryer-prolog/issues/95).

### Tabling (SLG resolution)

One of the foremost attractions of Prolog is that logical consequences
of pure&nbsp;programs can be derived by various execution strategies
that differ regarding essential properties such as termination,
completeness and efficiency.

The default execution strategy of Prolog is depth-first search with
chronological backtracking. This strategy is very efficient. Its main
drawback is that it is *incomplete*: It may fail to find any solution
even if one exists.

Scryer Prolog supports an alternative execution strategy which is
called *tabling* and also known as tabled&nbsp;execution and
SLG&nbsp;resolution. To enable tabled execution for a predicate, use
[`library(tabling)`](src/lib/tabling.pl) and add a `(table)/1`
directive for the desired predicate indicator. For example, if we
write:

```
:- use_module(library(tabling)).
:- table a/0.

a :- a.
```

Then the query `?- a.` *terminates* (and fails), whereas it
does&nbsp;not terminate with the default execution strategy.

Scryer Prolog implements tabling via *delimited continuations* as
described in [*Tabling as a Library with Delimited
Control*](https://biblio.ugent.be/publication/6880648/file/6885145.pdf)
by Desouter&nbsp;et.&nbsp;al.

### Constraint Logic Programming (CLP)

Scryer Prolog provides excellent support for Constraint Logic
Programming&nbsp;(CLP), which is the amalgamation of
Logic&nbsp;Programming&nbsp;(LP) and Constraints.

In addition to built-in support for [`dif/2`](src/lib/dif.pl),
[`freeze/2`](src/lib/freeze.pl),
[CLP(B)](src/lib/clpb.pl) and [CLP(ℤ)](src/lib/clpz.pl),
Scryer provides a convenient way to implement new user-defined
constraints: *Attributed variables* are available via
[`library(atts)`](src/lib/atts.pl) as in SICStus&nbsp;Prolog,
which is one of the most sophisticated and fastest constraint systems
in existence. In [`library(iso_ext)`](src/lib/iso_ext.pl),
Scryer provides predicates for backtrackable (`bb_b_put/2`) and
non-backtrackable (`bb_put/2`) global variables, which are needed to
implement certain types of constraint&nbsp;solvers.

These features make Scryer Prolog an ideal platform for teaching,
learning and developing portable CLP&nbsp;applications.

### Modules

Scryer has a simple predicate-based module system. It provides a
way to separate units of code into distinct namespaces, for both
predicates and operators. See the files
[`src/lib/*.pl`](src/lib) for
examples.

At the time of this writing, many predicates reside in their own
modules that need to be imported before they can be used.
The modules that ship with Scryer&nbsp;Prolog are also called
*library*&nbsp;modules or *libraries*, and include:

* [`lists`](src/lib/lists.pl)
  providing `length/2`, `member/2`, `select/3`, `append/[2,3]`,
  `foldl/[4,5]`, `maplist/[2-9]`, `same_length/2`, `transpose/2` etc.
* [`dcgs`](src/lib/dcgs.pl)
  Definite Clause Grammars (DCGs), a built-in grammar mechanism
  that uses the operator `(-->)/2` to define grammar rules,
  and the predicates `phrase/[2,3]` to invoke them.
* [`dif`](src/lib/dif.pl)
  The predicate `dif/2` provides declarative disequality:
  It is true if and only if its arguments are different, and
  delays the test until a sound decision can be made.
* [`reif`](src/lib/reif.pl)
  providing `if_/3`, `tfilter/3` and related predicates
  as described in *Indexing&nbsp;dif/2*.
* [`clpz`](src/lib/clpz.pl)
  CLP(ℤ): Constraint Logic Programming over Integers,
  providing declarative integer arithmetic via `(#=)/2`, `(#\=)/2`,
  `(#>=)/2` etc., and various global constraints and
  enumeration predicates for solving combinatorial tasks.
* [`pairs`](src/lib/pairs.pl)
  By convention, *pairs* are Prolog terms with
  principal&nbsp;functor `(-)/2`, written as `Key-Value`.
  This library provides `pairs_keys_values/3`,
  `pairs_keys/2`, and other predicates to reason about pairs.
* [`si`](src/lib/si.pl)
  The predicates `atom_si/1`, `integer_si/1`, `atomic_si/1`
  and `list_si/1` implement sound type checks. They raise
  instantiation errors if no decision can be made.
  They are declarative replacements for logically flawed
  lower-level type tests. For instance, instead of `integer(X)`,
  write `integer_si(X)` to ensure soundness of your programs.
  "si" stands for *sufficiently instantiated*, and also for
  *sound&nbsp;inference*.
* [`debug`](src/lib/debug.pl)
  Various predicates that allow for declarative debugging.
* [`pio`](src/lib/pio.pl)
  `phrase_from_file/2` applies a DCG nonterminal to the contents of a
  file, reading lazily only as much as is needed. Due to the compact
  internal string representation, also extremely large files can be
  efficiently processed with Scryer&nbsp;Prolog in this way.
* [`charsio`](src/lib/charsio.pl) Various predicates that are
  useful for parsing and reasoning about characters, notably
  `char_type/2` to classify characters according to their type.
* [`error`](src/lib/error.pl)
  `must_be/2` and `can_be/2` complement the type checks provided
  by `library(si)`, and are especially useful for Prolog library
  authors.
* [`tabling`](src/lib/tabling.pl)
  The operator `(table)/1` is used in directives that prepare
  predicates for tabled execution (SLG&nbsp;resolution).
* [`format`](src/lib/format.pl)
  The nonterminal `format_//2` is used to describe formatted output,
  arranging arguments according to a given format&nbsp;string.
  The predicates `format/[2,3]`, `portray_clause/[1,2]` and `listing/1`
  provide formatted *impure* output.
* [`assoc`](src/lib/assoc.pl)
  providing `empty_assoc/1`, `get_assoc/3`, `put_assoc/4` etc.
  to manage elements in AVL&nbsp;trees which ensure
  *O*(log(*N*))&nbsp;access.
* [`ordsets`](src/lib/ordsets.pl)
  represents ordered sets as lists.
* [`clpb`](src/lib/clpb.pl)
  CLP(B): Constraint Logic Programming over Boolean variables,
  a BDD-based SAT&nbsp;solver provided via the predicates
  `sat/1`, `taut/2`, `labeling/1` etc.
* [`arithmetic`](src/lib/arithmetic.pl)
  Arithmetic predicates such as `lsb/2`, `msb/2` and
  `number_to_rational/2`.
* [`time`](src/lib/time.pl) Predicates for reasoning about
  time, including `time/1` to measure the CPU&nbsp;time of a goal,
  `current_time/1` to obtain the current system time, the nonterminal
  `format_time//2` to describe strings with dates and times, and
  `sleep/1` to slow down a computation.
* [`cont`](src/lib/cont.pl)
  Provides *delimited continuations* via `reset/3` and `shift/1`.
* [`random`](src/lib/random.pl)
  Probabilistic predicates and random number generators.
* [`http/http_open`](src/lib/http/http_open.pl) Open a stream to
  read answers from web&nbsp;servers. HTTPS is also supported.
* [`sgml`](src/lib/sgml.pl)
  `load_html/3` represents HTML&nbsp;documents as Prolog&nbsp;terms
  for convenient and efficient reasoning.
* [`sockets`](src/lib/sockets.pl)
  Predicates for opening and accepting TCP connections as streams.
  TLS negotiation is performed via the option `tls(true)` in
  `socket_client_open/3`, yielding secure encrypted connections.
* [`crypto`](src/lib/crypto.pl)
  Cryptographically secure random numbers and hashes, HMAC-based
  key derivation (HKDF), password-based key derivation (PBKDF2),
  public key signatures and signature verification with Ed25519,
  authenticated encryption, and reasoning about elliptic curves.

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
:- module(test, [local_member/2]).
:- use_module(library(lists)).

local_member(X, Xs) :- member(X, Xs).
```

The user listing can also be terminated by placing `end_of_file.` at
the end of the stream.

### Configuration file

At startup, Scryer Prolog consults the file `~/.scryerrc`, if the file
exists. This file is useful to automatically load libraries and define
predicates that you need often.

For example, a sensible starting point for `~/.scryerrc` is:

```
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(reif)).
```
