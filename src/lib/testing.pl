/** Testing framework

This module provides the predicates `run_tests/0` and `run_tests/1` that can be used to do basic
unit testing.

# Getting started

Suppose you have a file `my_module.pl` with contents:

```prolog
:- module(my_module, [example/1]).

example(1). 
example(2). 
```

You could then write a `my_module_tests.pl` with contents:

```prolog
:- use_module(library(testing)).

:- use_module(my_module).

test("test 1 and 2", (
    example(1),
    example(2)
)).

test("test 3 and 4", (
    example(3),
    example(4)
)).
```

You can then run the tests with the following command:

```
$ scryer-prolog -f my_module_tests.pl -g run_tests
Running tests in module user.
  test "test 1 and 2" ... succeeded
  test "test 3 and 4" ... failed
```

And we can see that our test failed. We can filter just the failing test to investigate it better.

```
$ scryer-prolog -f my_module_tests.pl -g 'run_tests([filter("test 3 and 4")])'
Running tests in module user.
  test "test 3 and 4" ... failed
```

Adding `example(3). example(4).` to `my_module.pl` and rerunning the tests we see that it now
passes.

# How it works

This testing framework expects the tests to be written as predicates of the form
`test(-Name, -Goal)`. `Name` is the name of the test that can be used to identify and filter it,
`Goal` is the goal that needs to succeed for the test to pass.

By default `run_tests/1` only searches the `user` module for these test predicates, and so only
finds the tests that are written outside any module. You can use the `modules(+Modules)` option
to specify other modules it should search. This making it possible to write unit tests inside
modules, although this may lead to unexpected behavior because of limitations of the module system
and so it's not very recomended if you need to deal with metapredicates.

Errors and other exceptions make a test fail, but are reported to the user to help in debugging:

```
$ scryer-prolog -f my_module_tests.pl -g 'run_tests'
Running tests in module user.
  test "example with error" ... error(instantiation_error,functor/3)
  test "example with exception" ... exception(example_exception)
```

After running, `run_tests/1` exits with a status code of 0 if all tests that were run succeeded and
1 otherwise. This makes it possible to check if tests pass inside scripts.
*/

:- module(testing, [run_tests/0, run_tests/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(format)).
:- use_module(library(lambda)).
:- use_module(library(error)).

%% run_tests.
%
% Runs tests with default options. See `run_tests/1`.
run_tests :- run_tests([]).

%% run_tests(+Options).
%
% Runs tests with the options given in the list `Options`. Currently supported are:
%
% - `modules(+Modules)`: Runs the tests found in the given modules. Default: `[user]`. 
% - `filter(+Filter)`: Either `no_filter` to do no filtering or a string. Runs only the tests that
%    contain the string in their names. Default: `no_filter`.
% - `color(+Color)`: Either `true` or `false` to indicate if the output should be colored or not.
%   Default: `true`.
run_tests(Options) :-
    must_be(list, Options),
    options_option_default(Options, modules(Modules), [user]),
    options_option_default(Options, filter(Filter), no_filter),
    options_option_default(Options, color(Color), true),
    run_tests_opt(Modules, Color, Filter).

run_tests_opt(Modules, Color, Filter) :-
    maplist(module_mtests, Modules, MTests),
    maplist(
        [Color,Filter]+\(Module-Tests)^Succ^run_tests_module_opt(Module, Tests, Color, Filter, Succ),
        MTests,
        Successes
    ),
    (   all_succeeded(Successes) ->
        halt
    ;   halt(1)
    ).

module_tests(Module, Tests) :-
    catch(
        findall(
            test(Name, Module:Goal),
            (
                % Workaround. See: https://github.com/mthom/scryer-prolog/issues/2826
                G0 = Module:test(Name, Goal),
                call(G0)
            ),
            Tests
        ),
        error(existence_error(procedure,_),_),
        Tests = []
    ),
    true.

module_mtests(Module, MTests) :-
    module_tests(Module, Tests),
    MTests = Module-Tests.

all_succeeded([]).
all_succeeded([true|Succs]) :- all_succeeded(Succs).

run_tests_module_opt(Module, Tests0, Color, Filter, Success) :-
    filter_tests(Filter, Tests0, Tests),
    portray((
        "Running tests in module ",
        ansi(Color, white), format_("~q", [Module]), ansi(Color, reset),
        ".\n"
    )),
    run_tests_(Tests, Color, true, Success).

options_option_default(Options, Option, Default) :-
    (   member(Option, Options) ->
        true
    ;   Option =.. [_, Default]
    ).

run_tests_([], _, Success, Success).
run_tests_([test(Name, Goal)|Tests], Color, Success0, Success) :-
    portray(format_("  test \"~s\" ... ", [Name])),
    (   catch(call(Goal), Exception, true) ->
        (   nonvar(Exception) ->
            portray(ansi(Color, red)),
            (   Exception = error(_,_) ->
                portray(format_("~q", [Exception]))
            ;   portray(format_("exception(~q)", [Exception]))
            ),
            portray(ansi(Color, reset)),
            Success1 = false
        ;   portray((ansi(Color, green), "succeeded", ansi(Color, reset))),
            Success1 = Success0
        )
    ;   portray((ansi(Color, red), "failed", ansi(Color, reset))),
        Success1 = false
    ),
    portray("\n"),
    run_tests_(Tests, Color, Success1, Success).

ansi(true, reset) --> "\x1b\[0m".
ansi(true, red) --> "\x1b\[31;1m".
ansi(true, green) --> "\x1b\[32;1m".
ansi(true, white) --> "\x1b\[37;1m".
ansi(false, _) --> [].

portray(GRBody) :-
    phrase_to_stream(GRBody, user_output).

filter_tests(Filter, Tests0, Tests) :-
    (   Filter == no_filter ->
        Tests = Tests0
    ;   phrase(filter_tests_(Tests0, Filter), Tests)
    ).

filter_tests_([], _) --> [].
filter_tests_([test(Name, Body)|Tests], Filter) -->
    (   { phrase((..., Filter, ...), Name) } ->
        [test(Name, Body)]
    ;   []
    ),
    filter_tests_(Tests, Filter).
