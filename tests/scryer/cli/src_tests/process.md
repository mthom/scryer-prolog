```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [invalid, process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[invalid,process(P)]),process_kill(P),halt causes: error(domain_error(process_create_option,invalid),[predicate-process_create/3,predicate-check_options/3,predicate-must_be_known_options/3])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [invalid(_Var), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[invalid(_Var),process(P)]),process_kill(P),halt causes: error(domain_error(process_create_option,invalid),[predicate-process_create/3,predicate-check_options/3,predicate-must_be_known_options/3])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [stdin(null), stdin(null), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[stdin(null),stdin(null),process(P)]),process_kill(P),halt causes: error(domain_error(non_duplicate_options,stdin),[predicate-process_create/3,predicate-check_options/3,predicate-must_be_known_options/3])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [env([]), environment([]), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[env([]),environment([]),process(P)]),process_kill(P),halt causes: error(domain_error(non_conflicting_options,[env([]),environment([])]),[predicate-process_create/3,predicate-check_options/3,predicate-extract_options/2])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_wait(pid, _Status, [invalid(_Var), timeout(0)]), halt'
use_module(library(process)),process_wait(pid,_Status,[invalid(_Var),timeout(0)]),halt causes: error(domain_error(process_wait_option,invalid),[predicate-process_wait/3,predicate-check_options/3,predicate-must_be_known_options/3])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [stdin(invalid), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[stdin(invalid),process(P)]),process_kill(P),halt causes: error(domain_error(stdio_spec,invalid),[predicate-process_create/3,predicate-check_options/3,predicate-extract_options/2,predicate-valid_stdio/1])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_wait(50, _Status), halt'
use_module(library(process)),process_wait(50,_Status),halt causes: error(type_error(process,50),[predicate-process_wait/2,predicate-process_wait/3|process_wait/3])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_kill(50), halt'
use_module(library(process)),process_kill(50),halt causes: error(type_error(process,50),[predicate-process_kill/1|process_kill/1])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_id(50,_Pid), halt'
use_module(library(process)),process_id(50,_Pid),halt causes: error(type_error(process,50),[predicate-process_id/2|process_id/2])

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_release(50), halt'
use_module(library(process)),process_release(50),halt causes: error(type_error(process,50),[predicate-process_release/1,predicate-process_wait/2,predicate-process_wait/3|process_wait/3])

```
