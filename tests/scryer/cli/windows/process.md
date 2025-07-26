```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("cmd", ["/C", "exit", "1"], [process(P)]), process_wait(P, exit(1)), halt'

```
