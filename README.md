# rusty-wam

An implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf), ending in
pure Prolog.

## Progress

Pure Prolog is implemented as a simple REPL. "Pure Prolog" is Prolog
without cut, meta- or extra-logical operators, or side effects of any
kind. In terms of the tutorial pacing, the work has progressed to the
to the end of section 5.6, skipping past 5.4. Atoms and lists are the
only two data types currently supported.

## Tutorial
To enter a multi-clause predicate, the brackets ":{" and "}:" are used
as delimiters. They must be entirely contained with their own lines.

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
yes
X = _0
Y = x
Z = _2
Press ; to continue or . to abort.
```

Pressing ; will backtrack through other possible answers, if any exist.
Pressing . will abort the search and return to the prompt.

Wildcards work as well:

```
prolog> :{
member(X, [X|_]).
member(X, [_|Xs]) :- member(X, Xs).
}:
prolog> ?- member(X, [a, b, c]).
yes
X = a
Press ; to continue or . to abort.
;
X = b
Press ; to continue or . to abort.
;
X = c
Press ; to continue or . to abort.
;
no
```

Note that the values of variables belonging to successful queries are
printed out, on one line each. Uninstantiated variables are denoted by
a number preceded by an underscore (`X = _0` is an example in the
above).

## Occurs check

There's no occurs check, but there soon will be. Currently, attempting
unification on a cyclic term succeeds, and the attempt to write the
term to a string results in an infinite loop, ie.

```
prolog> p(W, W).
prolog> ?- p(f(f(W)), W).
yes
*loops to infinity*
```