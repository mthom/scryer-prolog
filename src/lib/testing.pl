:- module(testing, [run_tests/0, run_tests/1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(format)).
:- use_module(library(lambda)).
:- use_module(library(error)).

:- use_module(library(debug)).

run_tests :- run_tests([]).
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
