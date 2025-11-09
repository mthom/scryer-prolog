# Custom Toplevel Tests

## Basic -t halt functionality
Test that -t halt prevents entering REPL and exits cleanly

```trycmd
$ scryer-prolog -f --no-add-history -t halt
```

## -t halt with successful goal
Test that -t halt exits after running a goal successfully

```trycmd
$ scryer-prolog -f --no-add-history -g "write('Goal executed')" -t halt
Goal executed
```

## -t halt with failing goal
Test that -t halt still exits even when goal fails

```trycmd
$ scryer-prolog -f --no-add-history -g "fail" -t halt
% Warning: initialization failed for: fail

```

## Custom toplevel with exit code 0
Test custom toplevel that exits with code 0

```trycmd
$ scryer-prolog -f --no-add-history -t success_toplevel tests/scryer/cli/fixtures/toplevel_test_helper.pl
SUCCESS_TOPLEVEL_EXECUTED

```

## Custom toplevel with file loading
Test that custom toplevel can access predicates from loaded file

```trycmd
$ scryer-prolog -f --no-add-history -t test_file_loaded tests/scryer/cli/fixtures/toplevel_test_helper.pl
LOADED_PREDICATE_CALLED

```

## Custom toplevel with -g goal
Test combining -g goal with custom toplevel

```trycmd
$ scryer-prolog -f --no-add-history -g "helper_predicate" -t halt tests/scryer/cli/fixtures/toplevel_test_helper.pl
Helper predicate works

```

## Multiple goals with custom toplevel
Test multiple -g goals before custom toplevel

```trycmd
$ scryer-prolog -f --no-add-history -g "write('First goal'), nl" -g "write('Second goal'), nl" -t halt tests/scryer/cli/fixtures/toplevel_test_helper.pl
First goal
Second goal

```

## File loading then custom toplevel
Test that files are loaded before toplevel runs

```trycmd
$ scryer-prolog -f --no-add-history -t write_and_exit tests/scryer/cli/fixtures/toplevel_test_helper.pl
Output from custom toplevel

```

## Undefined toplevel predicate
Test error handling when toplevel predicate doesn't exist

```trycmd
$ scryer-prolog -f --no-add-history -t undefined_predicate
? failed
   error(existence_error(procedure,undefined_predicate/0),undefined_predicate/0).

```

## Test that default behavior unchanged
Without -t flag, a simple goal should still work (using halt to avoid REPL)

```trycmd
$ scryer-prolog -f --no-add-history -g "write('No custom toplevel'), nl, halt"
No custom toplevel

```

## g_caused_exception/2 with exception thrown
Test that g_caused_exception/2 is asserted when -g goal throws exception

```trycmd
$ scryer-prolog -f --no-add-history -g "throw(test_error)" -t check_exception_halt_1 tests/scryer/cli/fixtures/toplevel_test_helper.pl
? 1
throw(test_error) causes: test_error
EXCEPTION_CAUGHT
Goal: throw(test_error)
Exception: test_error

```

## g_caused_exception/2 with no exception
Test that g_caused_exception/2 is not asserted when -g goal succeeds

```trycmd
$ scryer-prolog -f --no-add-history -g "write('Success')" -t check_exception_halt_0 tests/scryer/cli/fixtures/toplevel_test_helper.pl
SuccessSUCCESS_NO_EXCEPTION

```

## g_caused_exception/2 with error() term
Test that g_caused_exception/2 captures error/2 terms correctly

```trycmd
$ scryer-prolog -f --no-add-history -g "throw(error(type_error(integer, foo), context))" -t check_exception_halt_1 tests/scryer/cli/fixtures/toplevel_test_helper.pl
? 1
throw(error(type_error(integer,foo),context)) causes: error(type_error(integer,foo),context)
EXCEPTION_CAUGHT
Goal: throw(error(type_error(integer,foo),context))
Exception: error(type_error(integer,foo),context)

```
