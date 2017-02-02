# rusty-wam

An implementation of the Warren Abstract Machine in Rust, done
according to the progression of languages in [Warren's Abstract
Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf), ending in
pure Prolog.

## Progress

The language L1 is implemented as a simple REPL. It supports
unification on facts and queries without backtracking and rules
without clauses, in the familiar Prolog syntax. No data types apart
from atoms are currently supported.

An example of the level of interaction currently supported is:

```
l1> p(Z, Z).  
l1> ?- p(Z, Z).  
yes  
l1> ?- p(Z, z).  
yes  
l1> ?- p(Z, w).  
yes  
l1> clouds(are, nice).
l1> ?- p(z, w).  
no  
l1> ?- p(w, w).  
yes
l1> ?- clouds(Z, Z).
no
l1> ?- clouds(Z, W).
yes
l1> ?- clouds(are, W).
yes
l1> ?- clouds(W, nice).
yes
l1> ?- clouds(nice, are).
no
l1> ?- p(Z, h(Z, W), f(W)).  
no  
l1> p(Z, h(Z, W), f(W)).  
l1> ?- p(z, h(z, z), f(w)).  
no  
l1> ?- p(z, h(z, w), f(w)).  
yes  
l1> ?- p(Z, h(z, W), f(w)).  
yes  
l1> ?- p(z, h(Z, w), f(w)).  
yes
l1> ?- p(Z, h(Z, w), f(Z)).
yes
l1> ?- p(z, h(Z, w), f(Z)).
no
l1> p(f(X), h(Y, f(a)), Y).
l1> ?- p(Z, h(Z, W), f(W)).
yes
l1> quit
```

## Occurs check

There's no occurs check, so cyclic terms do unify:

```
l1> p(W, W).
l1> ?- p(f(f(W)), W).
yes
```