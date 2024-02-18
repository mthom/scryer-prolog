
# Scryer Prolog

Scryer Prolog aims to become to ISO Prolog what GHC is to Haskell: an open
source industrial strength production environment that is also a
testbed for bleeding edge research in logic and constraint
programming, which is itself written in a high-level language.

**Scryer Prolog passes all tests** of
[syntactic&nbsp;conformity](https://www.complang.tuwien.ac.at/ulrich/iso-prolog/conformity_testing),
[`variable_names/1`](https://www.complang.tuwien.ac.at/ulrich/iso-prolog/variable_names) and
[`dif/2`](https://www.complang.tuwien.ac.at/ulrich/iso-prolog/dif).

The homepage of the project is: [**https://www.scryer.pl**](https://www.scryer.pl)

![Scryer Logo: Cryer](logo/scryer.png)

## Phase 1

Produce an implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial Reconstruction](https://github.com/mthom/scryer-prolog/blob/master/wambook/wambook.pdf).

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
      paper "[Indexing `dif/2`](https://arxiv.org/abs/1607.01590)".
- [x] All-solutions predicates (`findall/{3,4}`, `bagof/3`, `setof/3`, `forall/2`).
- [x] Clause creation and destruction (`asserta/1`, `assertz/1`,
      `retract/1`, `abolish/1`) with logical update semantics.
- [x] Backtrackable and non-backtrackable global variables via `bb_get/2`
      `bb_put/2` (non-backtrackable) and `bb_b_put/2`
      (backtrackable).
- [x] Delimited continuations based on reset/3, shift/1 (documented in
      "[Delimited Continuations for Prolog](https://biblio.ugent.be/publication/5646080/file/5646081)").
- [x] Tabling library based on delimited continuations
      (documented in "[Tabling as a Library with Delimited Control](https://biblio.ugent.be/publication/6880648/file/6885145.pdf)").
- [x] A _redone_ representation of strings as difference lists of
      characters, using a packed internal representation.
- [x] clp(B) and clp(ℤ) as builtin libraries.
- [x] Streams and predicates for stream control.
  - [x] A simple sockets library representing TCP connections as streams.
- [x] Incremental compilation and loading process, newly written,
      primarily in Prolog.
- [ ] Improvements to the WAM compiler and heap representation:
  - [ ] Replacing choice points pivoting on inlined semi-deterministic predicates
        (`atom`, `var`, etc) with if/else ladders. (_in progress_)
  - [ ] Inlining all built-ins and system call instructions.
  - [x] Greatly reducing the number of instructions used to compile disjunctives.
  - [ ] Storing short atoms to heap cells without writing them to the atom table.
- [ ] A compacting garbage collector satisfying the five properties of
      "[Precise Garbage Collection in Prolog](https://www.complang.tuwien.ac.at/ulrich/papers/PDF/2008-ciclops.pdf)." (_in progress_)
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
Roy's thesis, "[Can Logic Programming Execute as Fast as Imperative
Programming?](https://www.info.ucl.ac.be/~pvr/Peter.thesis/Peter.thesis.html)"

2. Add unum representation and arithmetic, using either an existing
unum implementation or an ad hoc one. Unums are described in
Gustafson's book "[The End of Error](http://www.johngustafson.net/unums.html)."

3. Add concurrent tables to manage shared references to atoms and
strings.

4. Add some form of JIT predicate indexing.

## Installing Scryer Prolog

### Binaries

Precompiled binaries for several platforms are available for download
at:

**https://github.com/mthom/scryer-prolog/releases/tag/v0.9.3**

### Native Compilation

First, install the latest stable version of
[Rust](https://www.rust-lang.org/en-US/install.html) using your
preferred method. Scryer tends to use features from newer Rust
releases, whereas Rust packages in Linux distributions, Macports,
etc. tend to lag behind. [rustup](http://rustup.rs) will keep your
Rust updated to the latest stable release; any existing Rust
distribution should be uninstalled from your system before rustup is
used.

Currently the only way to install the latest version of Scryer is to
clone directly from this git repository, and compile the system. This
can be done as follows:

```
$> git clone https://github.com/mthom/scryer-prolog
$> cd scryer-prolog
$> cargo build --release
```

The `--release` flag performs various optimizations, producing a
faster executable.

After compilation, the executable `scryer-prolog` is available in the
directory&nbsp;`target/release` and can be invoked to run the system.

On Windows, Scryer Prolog is easier to build inside a [MSYS2](https://www.msys2.org/)
environment as some crates may require native C compilation. However,
the resulting binary does not need MSYS2 to run. When executing Scryer in a shell, it is recommended to use a more advanced shell than mintty (the default MSYS2 shell). The [Windows Terminal](https://github.com/microsoft/terminal) works correctly.

To build a Windows Installer, you'll need first Scryer Prolog compiled in release mode, then, with WiX Toolset installed, execute:
```
candle.exe scryer-prolog.wxs
light.exe scryer-prolog.wixobj
```
It will generate a very basic MSI file which installs the main executable and a shortcut in the Start Menu. It can be installed with a double-click. To uninstall, go to the Control Panel and uninstall as usual.

Scryer Prolog must be built with **Rust 1.70 and up**.

### Building WebAssembly

Scryer Prolog has basic WebAssembly support. You can follow `wasm-pack`'s [official instructions](https://rustwasm.github.io/docs/wasm-pack/quickstart.html) to install `wasm-pack` and build it in any way you like.

However, none of the [default features](https://doc.rust-lang.org/cargo/reference/features.html#the-default-feature) are currently supported. The preferred way of disabling them is passing [extra options](https://rustwasm.github.io/wasm-pack/book/commands/build.html#extra-options) to `wasm-pack`.

For example, if you want a minimal working package without using any bundler like `webpack`, you can do this:
```
wasm-pack build --target web -- --no-default-features
```
Then a `pkg` directory will be created, containing everything you need for a webapp. You can test whether the package is successfully built by creating an html file, adapted from `wasm-bindgen`'s [official example](https://rustwasm.github.io/wasm-bindgen/examples/without-a-bundler.html) like this:

```html
<!DOCTYPE html>
<html>
    <head>
        <meta charset="UTF-8" />
        <title>Scryer Prolog - Sudoku Solver Example</title>
        <script type="module">
        import init, { eval_code } from './pkg/scryer_prolog.js';

        const run = async () => {
            await init("./pkg/scryer_prolog_bg.wasm");
            let code = `
            :- use_module(library(format)).
            :- use_module(library(clpz)).
            :- use_module(library(lists)).
            
            sudoku(Rows) :-
            length(Rows, 9), maplist(same_length(Rows), Rows),
            append(Rows, Vs), Vs ins 1..9,
            maplist(all_distinct, Rows),
            transpose(Rows, Columns),
            maplist(all_distinct, Columns),
            Rows = [As,Bs,Cs,Ds,Es,Fs,Gs,Hs,Is],
            blocks(As, Bs, Cs),
            blocks(Ds, Es, Fs),
            blocks(Gs, Hs, Is).
            
            blocks([], [], []).
            blocks([N1,N2,N3|Ns1], [N4,N5,N6|Ns2], [N7,N8,N9|Ns3]) :-
            all_distinct([N1,N2,N3,N4,N5,N6,N7,N8,N9]),
            blocks(Ns1, Ns2, Ns3).
            
            problem(1, [[_,_,_,_,_,_,_,_,_],
                        [_,_,_,_,_,3,_,8,5],
                        [_,_,1,_,2,_,_,_,_],
                        [_,_,_,5,_,7,_,_,_],
                        [_,_,4,_,_,_,1,_,_],
                        [_,9,_,_,_,_,_,_,_],
                        [5,_,_,_,_,_,_,7,3],
                        [_,_,2,_,1,_,_,_,_],
                        [_,_,_,_,4,_,_,_,9]]).
            
            main :-
            problem(1, Rows), sudoku(Rows), maplist(portray_clause, Rows).
            
            :- initialization(main).
            `;
            const result = eval_code(code);
            document.write(`<p>Sudoku solver returns:</p><pre>${result}</pre>`);
        }
        run();
        </script>    
    </head>
    <body></body>
</html>
```

Then you can serve it with your favorite http server like `python -m http.server` or `npx serve`, and access the page with your browser.

### Docker Install

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

Press `SPACE` to show further answers, if any exist. Press `RETURN`
or&nbsp;`.` to abort the search and return to the
toplevel&nbsp;prompt. Press&nbsp;`f` to see up to the next multiple of
5 answers, and `a` to see all answers. Press&nbsp;`h` to show a help
message.

Use `TAB` to complete atoms and predicate names in queries. For
instance, after consulting the program above, typing `decl` followed
by&nbsp;`TAB` yields `declarative_world`. Press&nbsp;`TAB` repeatedly
to cycle through alternative completions.

To quit Scryer Prolog, use the standard predicate `halt/0`:

```
?- halt.
```

### Starting Scryer Prolog

Scryer Prolog can be started from the command line by specifying
options, files and additional arguments. All components are optional:

<pre>
scryer-prolog [OPTIONS] [FILES] [-- ARGUMENTS]
</pre>

The supported options are:

```
   -h, --help             Display help message
   -v, --version          Print version information and exit
   -g, --goal GOAL        Run the query GOAL after consulting files
   -f                     Fast startup. Do not load initialization file (~/.scryerrc)
   --no-add-history       Prevent adding input to history file (~/.scryer_history)
```

All specified Prolog files are consulted.

After Prolog files, application-specific arguments can be specified on
the command line. These arguments can be accessed from within Prolog
applications with the predicate&nbsp;`argv/1`, which yields the list
of arguments represented as strings.

Prolog files can also be turned into *shell&nbsp;scripts* as explained in
https://github.com/mthom/scryer-prolog/issues/2170#issuecomment-1821713993.

### Dynamic operators

Scryer supports dynamic operators. Using the built-in
arithmetic operators with the usual precedences,

```
?- write_canonical(-5 + 3 - (2 * 4) // 8), nl.
-(+(-5,3),//(*(2,4),8))
   true.
```

New operators can be defined using the `op` declaration.

### First instantiated argument indexing

Scryer Prolog indexes on the leftmost argument that is not a variable
in all clauses of a predicate's&nbsp;definition. We call this strategy
first *instantiated* argument indexing.

A key motivation for first instantiated argument indexing is to enable
indexing for meta-predicates such as `maplist/N` and `foldl/N`, whose
first argument is a partial goal that is a variable in the definition
of these predicates and therefore cannot be used for indexing.

For example, a natural definition of `maplist/2` reads:

```
maplist(_, []).
maplist(Goal_1, [L|Ls]) :-
        call(Goal_1, L),
        maplist(Goal_1, Ls).
```

In this case, first instantiated argument indexing automatically uses
the *second* argument for indexing, and thus prevents choicepoints for
calls with lists of fixed lengths (and deterministic goals).
Conveniently, no auxiliary predicates with reordered arguments are
needed to benefit from indexing in such cases.

Conventional first argument&nbsp;indexing naturally arises as a
special case of this strategy, if the first argument is instantiated
in any clause of a predicate's definition.

### Strings and partial strings

A very compact internal representation of *strings* is one of the key
innovations of Scryer Prolog. This means that terms which appear as
lists of characters to Prolog programs are stored in packed
UTF-8&nbsp;encoding by the engine.

Without this innovation, storing a list of characters in memory would
use one WAM memory&nbsp;cell per character, one cell per list
constructor, and one cell for each tail that occurs in the list. Since
one cell takes 8&nbsp;bytes in the WAM as implemented by
Scryer&nbsp;Prolog, the packed representation yields an up&nbsp;to
**24-fold&nbsp;reduction** of memory usage, and corresponding
reduction of memory&nbsp;accesses when creating and processing
strings.

Scryer Prolog's compact internal string representation makes it
ideally suited for the use case Prolog was originally developed for:
efficient and convenient text processing, especially with definite
clause grammars (DCGs) as provided by
[`library(dcgs)`](src/lib/dcgs.pl) and
[`library(pio)`](src/lib/pio.pl) to transparently apply DCGs to files.

In Scryer Prolog, the default value of the Prolog flag `double_quotes`
is `chars`, which is also the recommended setting. This means that
lists of characters can be written as double-quoted strings, in the
tradition of Marseille&nbsp;Prolog.

For example, the following query succeeds:

```
?- "abc" = [a,b,c].
   true.
```

This shows that the string `"abc"`, which is represented as a sequence
of 3&nbsp;bytes internally, appears to Prolog programs as a list of
characters.

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

The efficient internal representation of strings and partial strings
was first proposed and explained by Ulrich Neumerkel in
issues&nbsp;[#24](https://github.com/mthom/scryer-prolog/issues/24)
and&nbsp;[#95](https://github.com/mthom/scryer-prolog/issues/95), and
Scryer&nbsp;Prolog is the first Prolog&nbsp;system that implements it.

### Occurs check and cyclic terms

The *occurs&nbsp;check* is an element of algorithms that perform
syntactic unification, causing the unification to fail if a variable
is unified with a term that contains that variable as a proper
subterm. For efficiency, the *occurs&nbsp;check* is omitted by default
in Scryer&nbsp;Prolog and many other Prolog systems.

In Scryer Prolog, performing unifications which succeed only if the
*occurs&nbsp;check* is omitted yield *cyclic&nbsp;terms*, also called
*rational&nbsp;trees*. For example:

```
?- X = f(X), Y = g(X,Y).
   X = f(X), Y = g(f(X),Y).
```

The creation of cyclic terms often indicates a programming mistake in
the formulation of Prolog predicates, and to obtain logically sound
results it is desirable to either perform all unifications with
*occurs&nbsp;check* enabled, or let Prolog throw an error if enabling
the *occurs&nbsp;check* is necessary to prevent a unification.

Scryer Prolog supports this via the Prolog flag `occurs_check`. It can
be set to one of the following values to obtain the desired behaviour:

- `false`
  Do not perform the *occurs&nbsp;check*. This is the default.
- `true`
  Perform all unifications with the *occurs&nbsp;check* enabled.
- `error`
  Yield an error if a unification is performed that the
  *occurs&nbsp;check* would have prevented.

Especially when starting with Prolog, we recommend to add the
following directive to the `~/.scryerrc` configuration file so that
programming mistakes in predicates that lead to the creation of cyclic
terms are indicated by errors:

```
:- set_prolog_flag(occurs_check, error).
```

Scryer Prolog implements specialized reasoning to make unifications
fast in many frequently occurring situations also if the
*occurs&nbsp;check* is enabled.

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
  `phrase_to_file/2` and `phrase_to_stream/2` write lists of
  characters described by DCGs to files and streams, respectively.
* [`lambda`](src/lib/lambda.pl)
  Lambda expressions to simplify higher order programming.
* [`charsio`](src/lib/charsio.pl) Various predicates that are useful
  for parsing and reasoning about characters, notably `char_type/2` to
  classify characters according to their type, and conversion
  predicates for different encodings of strings.
* [`error`](src/lib/error.pl)
  `must_be/2` and `can_be/2` complement the type checks provided by
  [`library(si)`](src/lib/si.pl), and are especially useful for
  Prolog library authors.
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
* [`files`](src/lib/files.pl)
  Predicates for reasoning about files and directories, such as
  `directory_files/2`, `file_exists/1` and `file_size/2`.
* [`cont`](src/lib/cont.pl)
  Provides *delimited continuations* via `reset/3` and `shift/1`.
* [`random`](src/lib/random.pl)
  Probabilistic predicates and random number generators.
* [`http/http_open`](src/lib/http/http_open.pl) Open a stream to
  read answers from web&nbsp;servers. HTTPS is also supported.
* [`http/http_server`](src/lib/http/http_server.pl) Runs a HTTP/1.1 and HTTP/2.0 web server. Uses [Warp](https://github.com/seanmonstar/warp) as a backend. Supports some query and form handling.
* [`sgml`](src/lib/sgml.pl)
  `load_html/3` and `load_xml/3` represent HTML and XML&nbsp;documents
  as Prolog&nbsp;terms for convenient and efficient reasoning. Use
  [`library(xpath)`](src/lib/iso_ext.pl) to extract information from
  parsed documents.
* [`csv`](src/lib/csv.pl)
  `parse_csv//1` and `parse_csv//2` can be used with [`phrase_from_file/2`](src/lib/pio.pl)
  or [`phrase/2`](src/lib/dcgs.pl) to parse csv
* [`serialization/abnf`](src/lib/serialization/abnf.pl)
  DCGs describing the
  [ABNF grammar core (RFC 5234)](https://tools.ietf.org/html/rfc5234#appendix-B.1),
  which is used to describe many [IETF](https://www.ietf.org/standards/rfcs/)
  syntaxes, such as [HTTP v1.1](https://www.rfc-editor.org/rfc/rfc7230.html#page-82),
  [SMTP](https://www.rfc-editor.org/rfc/rfc5321.html),
  [iCalendar](https://www.rfc-editor.org/rfc/rfc5545.html), and more.
* [`serialization/json`](src/lib/serialization/json.pl)
  `json_chars//1` can be used with [`phrase_from_file/2`](src/lib/pio.pl)
  or [`phrase/2`](src/lib/dcgs.pl) to parse and generate
  [JSON](https://www.json.org/json-en.html).
* [`xpath`](src/lib/xpath.pl)
  The predicate `xpath/3` is used for convenient reasoning about HTML
  and XML&nbsp;documents, inspired by the XPath language. This library
  is often used together with [`library(sgml)`](src/lib/sgml.pl).
* [`sockets`](src/lib/sockets.pl)
  Predicates for opening and accepting TCP connections as streams.
* [`os`](src/lib/os.pl)
  Predicates for reasoning about environment&nbsp;variables.
* [`iso_ext`](src/lib/iso_ext.pl)
  Conforming extensions to and candidates for inclusion in the Prolog
  ISO&nbsp;standard, such as `setup_call_cleanup/3`, `call_nth/2` and
  `call_with_inference_limit/3`.
* [`crypto`](src/lib/crypto.pl)
  Cryptographically secure random numbers and hashes, HMAC-based key
  derivation&nbsp;(HKDF), password-based key derivation&nbsp;(PBKDF2),
  public key signatures and signature verification with&nbsp;Ed25519,
  ECDH key&nbsp;exchange over Curve25519 (X25519), authenticated symmetric
  encryption with ChaCha20-Poly1305, and reasoning about elliptic curves.
* [`uuid`](src/lib/uuid.pl) UUIDv4 generation and hex representation
* [`tls`](src/lib/tls.pl)
  Predicates for negotiating TLS connections explicitly.
* [`ugraphs`](src/lib/ugraphs.pl) Graph manipulation library
* [`simplex`](src/lib/simplex.pl) Providing `assignment/2`,
  `transportation/4` and other predicates for solving linear
  programming problems.

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

### Development environment

To write and edit Prolog programs, we recommend
[GNU&nbsp;Emacs](https://www.gnu.org/software/emacs/) with the
[Prolog&nbsp;mode](https://bruda.ca/emacs/prolog_mode_for_emacs)
maintained by Stefan Bruda.

Use [ediprolog](https://www.metalevel.at/ediprolog/) to consult
Prolog&nbsp;code and evaluate Prolog queries in arbitrary
Emacs&nbsp;buffers.

Emacs definitions that show Prolog terms as trees are available
in&nbsp;[tools](tools).

To *debug* Prolog code, we recommend the predicates from
[**`library(debug)`**](src/lib/debug.pl), most notably:

- `(*)/1` to *"generalize&nbsp;away"* a Prolog goal. Use it to debug
  unexpected failures by generalizing your definitions until they
  succeed. Simply place&nbsp;`*` in front of a goal to generalize it away.
- `($)/1` to emit a *trace* of the execution, showing when a goal
  is invoked, and when it has succeeded. Place&nbsp;`$` in front of a goal
  to emit this information for that goal.

This way of debugging Prolog code has several major benefits, such as:
It stays close to the actual Prolog code under consideration, it does
not need additional tools and formalisms for its application, and
further, it encourages declarative reasoning that can in principle
also be performed automatically.

## Applications

Scryer Prolog's strong commitment to the Prolog ISO standard makes it
ideally suited for use in corporations and government&nbsp;agencies
that are subject to strict regulations pertaining to interoperability,
standards&nbsp;compliance and warranty.

Successful existing applications of Scryer Prolog include the
[DocLog](https://github.com/aarroyoc/doclog)&nbsp;system which
generates Scryer's own documentation and homepage, [Symbolic
Analysis of Grants](https://www.brz.gv.at/en/BRZ-Tech-Blog/Tech-Blog-7-Symbolic-Analysis-of-Grants.html)
by the Austrian Federal Computing Center, and parts of the
[precautionary](https://github.com/dcnorris/precautionary/tree/main/exec/prolog)
package for the analysis of dose-escalation trials in the
safety-critical and highly regulated domain of oncology
trial&nbsp;design, described in [*An Executable Specification of
Oncology Dose-Escalation Protocols with&nbsp;Prolog*](https://arxiv.org/abs/2402.08334).

Scryer Prolog is also very well suited for teaching and learning
Prolog, and for testing syntactic conformance and hence portability of
existing Prolog&nbsp;programs.

## Support and discussions

If Scryer Prolog crashes or yields unexpected errors, consider filing
an&nbsp;[issue](https://github.com/mthom/scryer-prolog/issues).

To get in touch with the Scryer Prolog community, participate in
[discussions](https://github.com/mthom/scryer-prolog/discussions)
or visit our #scryer IRC channel on [Libera](https://libera.chat)!
