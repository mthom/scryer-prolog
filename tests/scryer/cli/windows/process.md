```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("cmd", ["/C", "exit", "1"], [process(P)]), process_id(P, Pid), write(pid=Pid), nl, process_wait(P, exit(1)), halt'
pid=[..]

```

```trycmd
$  scryer-prolog -f --no-add-history -g 'use_module(library(process)), use_module(library(format)), process_create("cmd", [], [process(P), stdout(null), stdin(pipe(S))]), format(S, "exit 1~n", []), process_wait(P, exit(1)), halt'

```

```trycmd
$ scryer-prolog -f --no-add-history -t halt -g 'use_module(library(process)), process_create("cmd", ["/C", "exit", "1"], [process(P)]), process_id(P, Pid), write(pid=Pid), nl, process_wait(P, exit(1)), process_id(P, Pid2), write(pid=Pid2), nl'
pid=[..]
pid=[..]

```

domain error is expected as the release option has not yet been added
```trycmd
$ scryer-prolog -f --no-add-history -t halt -g 'use_module(library(process)), process_create("cmd", ["/C", "exit", "1"], [process(P)]), process_id(P, Pid), write(pid=Pid), nl, process_wait(P, exit(1), [release(false)]), process_id(P, Pid2), write(pid=Pid2), nl, process_release(P), process_id(P, Pid3), write(pid=Pid3), nl'
pid=[..]
use_module(library(process)),process_create("cmd",["/C","exit","1"],[process(P)]),process_id(P,Pid),write(pid=Pid),nl,process_wait(P,exit(1),[release(false)]),process_id(P,Pid2),write(pid=Pid2),nl,process_release(P),process_id(P,Pid3),write(pid=Pid3),nl causes: error(domain_error(process_wait_option,release),[predicate-process_wait/3,predicate-check_options/3,predicate-must_be_known_options/3])

```