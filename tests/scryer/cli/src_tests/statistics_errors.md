`statistics/2` with an unknown key must raise a `domain_error`, not fail
silently (issue #3427). This matches SICStus, GNU Prolog and SWI.

An unknown atom key raises `domain_error(statistics_key, Key)`:

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(time)), catch(statistics(nonsense,_), E, (write(E), nl)), halt"
error(domain_error(statistics_key,nonsense),statistics/2)

```

An unbound key raises an instantiation error:

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(time)), catch(statistics(_,_), E, (write(E), nl)), halt"
error(instantiation_error,statistics/2)

```

A non-atom key raises a type error:

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(time)), catch(statistics(123,_), E, (write(E), nl)), halt"
error(type_error(atom,123),statistics/2)

```

The supported `runtime` key still succeeds:

```trycmd
$ scryer-prolog -f --no-add-history -g "use_module(library(time)), statistics(runtime, [T,U]), number(T), write(runtime_ok(U)), nl, halt"
runtime_ok(unsupported)

```
