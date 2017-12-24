# rusty-wam

## Phase 1

An implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf).

Phase 1 has been completed, in that rusty-wam implements in some form
all of the WAM book, including lists, cuts, Debray allocation, first
argument indexing, and conjunctive queries.

## Phase 2

Extend rusty-wam to include the following, among other features:

* call/N as a built-in meta-predicate (_done_).
* ISO Prolog compliant throw/catch (_done_).
* Built-in and user-defined operators of all fixities, with custom
  associativity and precedence (_done_). 
* Bignum, rational number and floating point arithmetic (_in progress_).
* Built-in control operators (`,`, `;`, `->`, etc.) (_in progress_).
* Built-in predicates for list processing and top-level declarative
  control (`setup_call_control/3`, `call_with_inference_limit/3`,
  etc.)
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

Use the WAM code produced by the completed code generator to target LLVM
IR to get JIT-compiled and -executed Prolog programs.

It's my hope to use rusty-wam as the logic engine of a low level (and
ideally, very fast) [Shen](http://shenlanguage.org) implementation.

## Nice to have features

There are no current plans to implement any of these, but they might be
nice to have in the future. They'd make a good project for anyone wanting
to contribute code to rusty-wam.

1. Add the global analysis techniques of Peter van Roy's thesis, "Can
Logic Programming Execute as Fast as Imperative Programming?"

2. Add unum representation and arithmetic, as described in Gustafson's
book "The End of Error."

3. Add support for shift/reset delimited continuations, see "Delimited Continuations
for Prolog."

4. Add an incremental compacting garbage collector the heap.

5. Add a concurrent atom table.

## Built-in predicates

The following predicates are built-in to rusty-wam.

* Arithmetic support:
    * is/2 works for `(+)/2`, `(-)/{1,2}`, `(*)/2`, `(//)/2`, `(div)/2`, `(/)/2`, `(rdiv)/2`,
      `(xor)/2`, `(rem)/2`, `(mod)/2`, `(/\)/2`, `(\/)/2`, `(>>)/2`, `(<<)/2`.
    * Comparison operators: `>`, `<`, `=<`, `>=`, `=:=`, `=\=`.
* `atomic/1`
* `call/N` (1 <= N <= 63)
* `catch/3`
* `duplicate_term/2`
* `false/0`
* `(\+)/1`
* `(=)/2`
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
true
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

Lastly, rusty-wam supports dynamic operators. Using the built-in
arithmetic operators with the usual precedences,

```
prolog> ?- X = -5 + 3 - (2 * 4) // 8.
true.
X = -(+(-(5), 3), //(*(2, 4), 8)).
```