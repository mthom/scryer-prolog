Asserting clauses containing arena objects such as streams must not panic:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_output(S), assertz(s(S)), s(X), X == S, write(ok), nl, halt.'
ok

```

Clauses holding distinct streams are indexed by identity:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_output(O), current_input(I), assertz(s(O)), assertz(s(I)), assertz(s(a)), findall(x, s(O), [x]), findall(x, s(I), [x]), write(ok), nl, halt.'
ok

```

A process handle inside a clause (the original report):

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("true", [], [process(P)]), asserta(process(P)), process(Q), Q == P, write(ok), nl, halt.'
ok

```

A server socket inside a clause is not representable as a term:

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(sockets)), socket_server_open(_, S), catch(asserta(mysock(S)), error(representation_error(term), asserta/1), true), write(ok), nl, halt.'
ok

```

A stream obtained through `functor/3`:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_input(S), functor(S, N, _), S == N, assertz(stream(N)), stream(M), M == S, write(ok), nl, halt.'
ok

```

Asserting a bare process handle is a type error, consistent with `callable/1`:

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("true", [], [process(P)]), \+ callable(P), catch(asserta(P), error(type_error(callable, _), asserta/1), true), write(ok), nl, halt.'
ok

```

Same for a bare stream:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_output(S), \+ callable(S), catch(asserta(S), error(type_error(callable, _), asserta/1), true), write(ok), nl, halt.'
ok

```

A stream as a body goal is a type error, not a panic:

```trycmd
$ scryer-prolog -f --no-add-history -g 'current_output(S), catch(asserta((h :- S)), error(type_error(callable, _), asserta/1), true), write(ok), nl, halt.'
ok

```

A released process handle inside a clause is not representable as a term:

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("false", [], [process(P)]), process_wait(P, exit(1)), catch(asserta(p(P)), error(representation_error(term), asserta/1), true), write(ok), nl, halt.'
ok

```
