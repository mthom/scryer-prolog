```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("false", [], [process(P)]), process_id(P, Pid), write(pid=Pid), nl, process_wait(P, exit(1)), halt'
pid=[..]

```

```trycmd
$  scryer-prolog -f --no-add-history -g 'use_module(library(process)), use_module(library(format)), process_create("sh", [], [process(P), stdout(null), stdin(pipe(S))]), format(S, "exit 1~n", []), process_wait(P, exit(1)), halt'

```

```trycmd
$  scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("sh", ["-c", "sleep 5"], [process(P), stdout(null)]), process_kill(P), process_wait(P, killed(9)), halt'

```

```trycmd
$ scryer-prolog -f --no-add-history -t halt -g 'use_module(library(process)), process_create("false", [], [process(P)]), process_id(P, Pid), write(pid=Pid), nl, process_wait(P, exit(1)), process_id(P, Pid2), write(pid=Pid2), nl'
? failed
pid=[..]
use_module(library(process)),process_create("false",[],[process(P)]),process_id(P,Pid),write(pid=Pid),nl,process_wait(P,exit(1)),process_id(P,Pid2),write(pid=Pid2),nl causes: error(existence_error(process,$dropped_value),[predicate-process_id/2|process_id/2])

```

```trycmd
$ scryer-prolog -f --no-add-history -t halt -g 'use_module(library(process)), process_create("false", [], [process(P)]), process_id(P, Pid), write(pid=Pid), nl, process_wait(P, exit(1), [release(false)]), process_id(P, Pid2), write(pid=Pid2), nl, process_release(P), process_id(P, Pid3), write(pid=Pid3), nl'
? failed
pid=[..]
pid=[..]
use_module(library(process)),process_create("false",[],[process(P)]),process_id(P,Pid),write(pid=Pid),nl,process_wait(P,exit(1),[release(false)]),process_id(P,Pid2),write(pid=Pid2),nl,process_release(P),process_id(P,Pid3),write(pid=Pid3),nl causes: error(existence_error(process,$dropped_value),[predicate-process_id/2|process_id/2])

```