```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("false", [], [process(P)]), process_wait(P, exit(1)), halt'

```

```trycmd
$  scryer-prolog -f --no-add-history -g 'use_module(library(process)), use_module(library(format)), process_create("sh", [], [process(P), stdout(null), stdin(pipe(S))]), format(S, "exit 1~n", []), process_wait(P, exit(1)), halt'

```

```trycmd
$  scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("sh", ["-c", "sleep 5"], [process(P), stdout(null)]), process_kill(P), process_wait(P, killed(9)), halt'

```