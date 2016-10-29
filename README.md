# rusty-wam

The beginnings of the Warren Abstract Machine in Rust, according to
the progression of languages in [Warren's Abstract Machine: A Tutorial
Reconstruction](http://wambook.sourceforge.net/wambook.pdf), ending in
pure Prolog.

## Progress

The language L0 is implemented as a simple REPL. It supports
unification on facts and queries without backtracking and clauses
without rules, in the familiar Prolog syntax. No data types apart from
atoms are currently supported.

An example of the level of interaction currently supported is:

```l0> p(Z, Z).
   Program stored.  
   l0> ?- p(Z, Z).  
   yes  
   l0> ?- p(Z, z).  
   yes  
   l0> ?- p(Z, w).  
   yes  
   l0> ?- p(z, w).  
   no  
   l0> ?- p(w, w).  
   yes  
   l0> ?- p(Z, w).  
   yes  
   l0> ?- p(Z, h(Z, W), f(W)).  
   no  
   l0> p(Z, h(Z, W), f(W)).  
   Program stored.  
   l0> ?- p(z, h(z, z), f(w)).  
   no  
   l0> ?- p(z, h(z, w), f(w)).  
   yes  
   l0> ?- p(Z, h(z, W), f(w)).  
   yes  
   l0> ?- p(z, h(Z, w), f(w)).  
   yes  
   l0> quit```