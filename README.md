# rusty-wam

An implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf), ending in
pure Prolog.

## Progress

Prolog is implemented as a simple REPL. It is without meta- or
extra-logical operators, or side effects of any kind, with the lone
exception of cut. In terms of the tutorial pacing, the work covers in
some form all of the WAM book, including lists, cuts, Debray
allocation, indexing, and conjunctive queries.

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
and so do conjunctive queries:

```
prolog> ?- member([X,X],[a,b,c,[d,d],[e,d]]), member(X, [a,b,c,d,e,f,g]), member(Y, [X, a, b, c, d]).
yes
Y = d
X = d
Press ; to continue or . to abort.
Y = a
X = d
Press ; to continue or . to abort.
Y = b
X = d
Press ; to continue or . to abort.
Y = c
X = d
Press ; to continue or . to abort.
Y = d
X = d
Press ; to continue or . to abort.
no
prolog>
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