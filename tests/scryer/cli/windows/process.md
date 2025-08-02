```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("cmd", ["/C", "exit", "1"], [process(P)]), process_wait(P, exit(1)), halt'

```

```trycmd
$  scryer-prolog -f --no-add-history -g 'use_module(library(process)), use_module(library(format)), process_create("cmd", [], [process(P), stdout(null), stdin(pipe(S))]), format(S, "exit 1~n", []), process_wait(P, exit(1)), halt'

```