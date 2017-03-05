# rusty-wam

An implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf), ending in
pure Prolog.

## Progress

The language L3 is implemented as a simple REPL. L3 is pure Prolog --
Prolog without cuts, meta- or extra-logical operators, or side effects
of any kind. No data types apart from atoms are currently supported.

## Tutorial
To enter a multi-clause predicate, the brackets ":{" and "}:" are used
as delimiters. They must be entirely contained with their own lines.

For example,
```
l3> :{
p(f(f(X)), h(W), Y) :- g(W), h(W), f(X).
p(X, Y, Z) :- h(Y), z(Z).
}:
l3> :{
h(x).
h(y).
h(z).
}:
```

Single clause predicates can entered without brackets, as in
```
l3> p(X) :- q(X).
l3> f(s).
l3> z(Z).
```

Queries are issued as
```
l3> ?- p(X, Y, Z).
```

Given the above work, the result of the query will be
```
l3> ?- p(X, Y, Z).
yes
X = _0
Y = x
Z = _2
Press ; to continue or A to abort.
```

Pressing ; will backtrack through other possible answers, if any exist.
Pressing A will abort the search and return to the prompt.

Note that the values of variables belonging to successful queries are
printed out, on one line each. Uninstantiated variables are denoted by
a number preceded by an underscore (X = _0 is an example in the
above).

## Occurs check

There's no occurs check, but there soon will be. Currently, attempting
unification on a cyclic term succeeds, and the attempt to write the
term to a string results in an infinite loop, ie.

```
l3> p(W, W).
l3> ?- p(f(f(W)), W).
yes
*loops to infinity*
```