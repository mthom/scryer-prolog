# rusty-wam

An implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf), ending in
pure Prolog.

## Progress

The language L2 is implemented as a simple REPL. It supports
unification on queries without backtracking, where rules and facts are
limited to a single name/arity pairing, in the familiar Prolog
syntax. No data types apart from atoms are currently supported.

An example of the level of interaction currently supported is:

```
l2> p(Z, Z).  
l2> ?- p(Z, Z).  
yes  
l2> ?- p(Z, z).  
yes  
l2> ?- p(Z, w).  
yes  
l2> clouds(are, nice).
l2> ?- p(z, w).  
no  
l2> ?- p(w, w).  
yes
l2> ?- clouds(Z, Z).
no
l2> ?- clouds(Z, W).
yes
l2> ?- clouds(are, W).
yes
l2> ?- clouds(W, nice).
yes
l2> ?- clouds(nice, are).
no
l2> ?- p(Z, h(Z, W), f(W)).  
no  
l2> p(Z, h(Z, W), f(W)).  
l2> ?- p(z, h(z, z), f(w)).  
no  
l2> ?- p(z, h(z, w), f(w)).  
yes  
l2> ?- p(Z, h(z, W), f(w)).  
yes  
l2> ?- p(z, h(Z, w), f(w)).  
yes
l2> ?- p(Z, h(Z, w), f(Z)).
yes
l2> ?- p(z, h(Z, w), f(Z)).
no
l2> p(f(X), h(Y, f(a)), Y).
l2> ?- p(Z, h(Z, W), f(W)).
yes
l2> p(X, Y) :- q(X, Z), r(Z, Y).
l2> q(q, s).
l2> r(s, t).
l2> ?- p(X, Y).
yes
l2> ?- p(q, t).
yes
l2> ?- p(t, q).
no
l2> ?- p(q, T).
yes
l2> ?- p(Q, t).
yes
l2> ?- p(t, t).
no
l2> quit
```

## Occurs check

There's no occurs check, so cyclic terms do unify:

```
l2> p(W, W).
l2> ?- p(f(f(W)), W).
yes
```