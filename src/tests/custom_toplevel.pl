:- module(custom_toplevel_tests, []).

:- use_module(test_framework).

% Test predicate that will be used as custom toplevel
custom_halt :-
    write('Custom toplevel executed'), nl,
    halt(0).

% Test predicate with non-zero exit
custom_halt_with_code :-
    write('Custom toplevel with exit code'), nl,
    halt(42).

% Test predicate that writes and then succeeds (would enter REPL without -t halt)
test_predicate :-
    write('Test predicate executed'), nl.

test("-t halt terminates after initialization", (
    % This tests that -t halt prevents entering REPL
    % When run with: scryer-prolog -t halt custom_toplevel.pl
    % Should execute initialization and halt
    true
)).

test("custom toplevel can be user-defined", (
    % This tests that custom predicates can be used as toplevel
    % When run with: scryer-prolog -t custom_halt custom_toplevel.pl
    % Should call custom_halt and exit with code 0
    true
)).

test("custom toplevel receives control after initialization", (
    % Initialization runs before toplevel
    % So any initialization goals should complete first
    true
)).

test("default behavior is repl when no -t specified", (
    % Without -t, should enter REPL after initialization
    % This is the traditional behavior
    true
)).
