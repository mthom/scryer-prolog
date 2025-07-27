```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [invalid, process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[invalid,process(P)]),process_kill(P),halt causes: error(domain_error(process_create_option,_[..]),process_create/3)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [invalid(_), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[invalid(_[..]),process(P)]),process_kill(P),halt causes: error(domain_error(process_create_option,invalid),process_create/3)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [stdin(null), stdin(null), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[stdin(null),stdin(null),process(P)]),process_kill(P),halt causes: error(domain_error(non_duplicate_options,stdin),process_create/3)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [env([]), environment([]), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[env([]),environment([]),process(P)]),process_kill(P),halt causes: error(domain_error(non_conflicting_options,[env([]),environment([])]),process_create/3)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_wait(pid, _, [invalid(_), timeout(0)]), halt'
use_module(library(process)),process_wait(pid,_[..],[invalid(_[..]),timeout(0)]),halt causes: error(domain_error(process_wait_option,invalid),process_wait/3)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_create("", [], [stdin(invalid), process(P)]), process_kill(P), halt'
use_module(library(process)),process_create([],[],[stdin(invalid),process(P)]),process_kill(P),halt causes: error(domain_error(stdio_spec,invalid),process_create/3)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_wait(50, _), halt'
use_module(library(process)),process_wait(50,_[..]),halt causes: error(type_error(process,50),process_wait/2)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_kill(50), halt'
use_module(library(process)),process_kill(50),halt causes: error(type_error(process,50),process_kill/1)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_id(50,_), halt'
use_module(library(process)),process_id(50,_[..]),halt causes: error(type_error(process,50),process_id/2)

```

```trycmd
$ scryer-prolog -f --no-add-history -g 'use_module(library(process)), process_release(50), halt'
use_module(library(process)),process_release(50),halt causes: error(type_error(process,50),process_wait/2)

```
