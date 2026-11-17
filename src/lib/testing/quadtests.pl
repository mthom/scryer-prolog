/** Quads — testing for Prolog modules.

## Introduction

A *quad* is a query paired with a description of its
expected answer:

```
?- emission_by_year(1999, [[_, _, 1999, 1], [_, _, _, _] | _], emission(1999, 1)).
   true.
```

The `?-` line is the goal. The line(s) beneath it are the *answer
description*: here, `true.` records that the goal succeeds. A quad
runner, `check_module_quads/2` or `evaluated_quads/2`, collects
each quad of a module and verifies that the goal's answers agree
with the description.

## Forms of an answer description with example

### `true.` and `false.`

A goal that should succeed is paired with `true.`; one that should
fail is paired with `false.`:

```
?- emission_by_year(1999, [[_, _, 1999, 1], [_, _, _, _] | _], emission(1999, 1)).
   true.

?- emission_by_year(2026, [[_, _, 1999, 1], [_, _, 2000, _]], _).
   false.
```

### Domain testing

A quad can also test the domain of a variable. Here we test that the emission data contains every year of interest.

```
?- emission_parsed_data(_, Data), year_interest(T), emission_by_year(T, Data, R), R == none.
   false.
```

### Bindings

When the goal binds variables, the expected bindings are written
exactly as the top level prints them:

```
?- emission_parsed_data(Head, _).
   Head = ["Entity", "Code", "Year", "Annual CO₂ emissions"].
```

### Multiple answers

```
?- year_with_emission_of(1, [[_, _, 2002, 1], [_, _, 2003, 2], [_, _, 2004, 1], [_, _, 2005, 1]], X).
   X = 2002
;  X = 2004
;  X = 2005 .
```

### Partial answer bags

To record only the first few answers without committing to the rest, end the alternatives with `...`:
```
?- year_with_emission_of(1, [[_, _, 2002, 1], [_, _, 2003, 2], [_, _, 2004, 1], [_, _, 2005, 1], [_, _, 2006, 1], [_, _, 2007, 3], [_, _, 2008, 1]], X).
   X = 2002
;  X = 2004
;  ... .
```


## Errors

A goal that should throw an error can be exercised with `catch/3`.

```
?- catch(phrase(jump_emission([[_, _, 2000, 1], [_, _, 1000, 2]]), _),
         error('the data is not ordered by year'),
         X = true).
   X = true.
```

## Setup and cleanup

A quad can set up state before its goal runs and clean it up
afterwards, for instance when files are generated:

```
?- use_module(library(files)),
   use_module(library(iso_ext)),
   _File = "mock_analysis.pl",
   catch(delete_file(_File), error(existence_error(file, _File), delete_file/1), true),
   _AnalysisToSave = [jump(1000, 2000, 1), jump(3000, 4000, 4)],
   setup_call_cleanup(
       saved_analysis(_AnalysisToSave, _File),
       (
           file_exists(_File),
           saved_analysis(_AnalysisLoaded, _File)
       ),
       delete_file(_File)
   ),
   _AnalysisToSave == _AnalysisLoaded.
   true.
```

## Running quads

This module exposes:

| `check_module_quads(+Module, -Quads)` | print a human-readable trace of each quad and fail at the first mismatch |
| `evaluated_quads(+Module, -Result)`   | return the passed and rejected quads of `Module` for further reasoning   |
*/

% Efforts toward literate tests with quads

:- module(quadtests, [check_module_quads/2, evaluated_quads/2]).

:- use_module(library(iso_ext)).
:- use_module(library(pio)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(reif)).
:- use_module(library(debug)).
:- use_module(library(lambda)).
:- use_module(library(error)).
:- use_module(library(time)).
:- use_module(library('testing/testutils')).
:- use_module(library('testing/special_functions')).

portray_term(Stream) :-
    read_term(Stream, Term, []),
    portray_clause(Term).

?- check_module_quads(special_functions, _).
% Checking 11 quads ..
% CHECKING.. (?-A=0.6174468790806071,erf(A,A),B is-A,erf(B,B)).
% CHECKING.. (?-try_falsify(odd_t(erf,real(A)))).
% CHECKING.. (?-witness(odd_t(erf,real(A),false))).
% CHECKING.. (?-witness((real(A),erf(A,B),erf(-A,C),abs(B+C)>0))).
% CHECKING.. (?-length(A,B)).
% CHECKING.. (?-real(A),erf(A,B),erfc(A,C),abs(B+C-1)>epsilon).
% CHECKING.. (?-try_falsify(δ_inverses_t(40*epsilon,erf,inverf,interval(-2,2,A)))).
% CHECKING.. (?-try_falsify(δ_inverses_t(40*epsilon,erfc,inverfc,interval(-2,2,A)))).
% CHECKING.. (?-A=10,B is A+1,gamma(B,C),int_realfact(A,D)).
% CHECKING.. (?-gamma_P_Q(1.2,2.3,A,B),abs(A+B-1)<epsilon).
% CHECKING.. (?-A=1.5,B=0.7,invgammp(A,B,C),gamma_P_Q(A,C,D,E),abs(B-D)<epsilon).
   true.

%% evaluated_quads(+Module, -Result).
%
%  Evaluate the quads of Module. Result is bound to a term of the form
%  evaluation(passed(Passed), rejected(Rejected)), where Passed and
%  Rejected are lists of the quads that succeeded and failed against
%  their expected answer description.
evaluated_quads(Module, evaluation(passed(Passed), rejected(Rejected))) :-
    use_module(Module),
    read_quads(Module, Quads),
    zip(Qs, ADs, Quads),
    phrase(evaluate_qd_ads(Module, Qs, ADs), R),
    phrase(assemble_passed_response(R), Passed),
    phrase(assemble_rejected_response(R), Rejected).

evaluate_qd_ads(Module, [Q|Qr], [A|Ar]) --> {check_qu_ad_(Module, Q, A, _)}, [passed(Q)], evaluate_qd_ads(Module, Qr, Ar).
evaluate_qd_ads(Module, [Q|Qr], [A|Ar]) --> { \+ check_qu_ad_(Module, Q, A, _)}, [rejected(Q)], evaluate_qd_ads(Module, Qr, Ar).
evaluate_qd_ads(_, [], []) --> [].

assemble_passed_response([passed(X)|R]) --> [X], assemble_passed_response(R).
assemble_passed_response([rejected(_)|R]) --> [], assemble_passed_response(R).
assemble_passed_response([]) --> [].

assemble_rejected_response([rejected(X)|R]) --> [X], assemble_rejected_response(R).
assemble_rejected_response([passed(_)|R]) --> [], assemble_rejected_response(R).
assemble_rejected_response([]) --> [].

%% check_module_quads(+Module, -Quads).
%
%  Evaluate the quads of Module, printing a human-readable trace of
%  each quad to the top level. Fails as soon as a quad does not match
%  its expected answer description, without checking subsequent quads.
%  Quads is bound to the list of quads read from Module.
check_module_quads(Module, Quads) :-
    use_module(Module),
    read_quads(Module, Quads),
    zip(Qs, ADs, Quads),
    length(Qs, NQ),
    format("% Checking ~d quads ..~n", [NQ]),
    maplist(check_qu_ad(Module), Qs, ADs).

read_quads(Module, Quads) :-
    module_terms(Module, Terms),
    terms_quads(Terms, Quads).

module_terms(Module, Terms) :-
    module_file(Module, File),
    setup_call_cleanup(
        open(File, read, Stream, [type(text)]),
        read_terms(Stream, Terms),
        close(Stream)
    ).

module_file(Module, File) :- atom_concat(Module, '.pl', File).

% Given a list of terms, filter out the predicate clauses.
% TODO: Arg 1 is really a list of Term-VarNames _pairs_;
%       it would be very nice to find a less unsightly
%       name than 'TermVN' for these!
terms_quads([Term|Terms], Quads) :-
    (   term_type(Term, clause) -> terms_quads(Terms, Quads)
    ;   Quads = [Term|Quads_],
        terms_quads(Terms, Quads_)
    ).
terms_quads([], []).

term_type(Term-_, Type) :-
    (   Term = (?- _) -> Type = query
    ;   Term = (_,_) -> Type = answer_description
    ;   Term = (_;_) -> Type = answer_description
    ;   Term = (_ = _) -> Type = answer_description
    ;   Term == true -> Type = answer_description
    ;   Term == false -> Type = answer_description
    ;   Type = clause
    ).

?- term_type(test("erf is odd",try_falsify(odd_t(erf,real(_L))))-_, Type).
   Type = clause.

read_terms(Stream, Terms) :-
    read_terms_(Stream, [], Terms).
read_terms_(Stream, Terms0, Terms) :-
    Options = [variable_names(VarNames)],
    read_term(Stream, Term, Options),
    (   Term = end_of_file -> reverse(Terms0, Terms)
    ;   read_terms_(Stream, [Term-VarNames|Terms0], Terms)
    ).

%% zip(+Xs, +Ys, ?XYs)
%% zip(?Xs, ?Ys, +XYs)
%
% List XYs interleaves same-length lists Xs and Ys.
zip([X|Xs], [Y|Ys], [X,Y|XYs]) :-
    zip(Xs, Ys, XYs).
zip([], [], []).

?- zip(Xs, Ys, XYs). % MGQ does not terminate
   error('$interrupt_thrown',repl/0).

% The following suggested by Ulrich via Quad Works chat
?- zip(Xs, Ys, XYs), false. % loops

?- zip(X, [4,5,6], [1,4,2,5,3,6]).
   X = [1,2,3].

?- zip([1,2,3], Y, [1,4,2,5,3,6]).
   Y = [4,5,6].

?- zip([1,2,3], [4,5,6], Z).
   Z = [1,4,2,5,3,6].

?- zip(Xs, Ys, [1,4,2,5,3,6]).
   Xs = [1,2,3], Ys = [4,5,6].

% 3. Demonstrate checking 1 quad, the top two elements of a QAs list.

check_qu_ad_(Module, Q-QVN, A-AVN, LitQ) :-
    Q = ?-(G),
    phrase(portray_clause_(Q), LitQ), % NB: LitQ terminates w/ newline
    (   A == true -> call(Module:G)
    ;   A == false -> (   call(Module:G) -> false
                      ;   true
                      )
    ;   phrase(unconj(A), As) ->
        (   length(As, N),
            n_answers(N, A, AVN, ADs),
            n_answers(N, Module:G, QVN, Answers),
            maplist(contains, ADs, Answers)
        )
    ;   % Otherwise, we have the ',' case of a solitary answer
        call(Module:G),
        call(A),
        QVN == AVN
    ).

check_qu_ad(Module, Q-QVN, A-AVN) :-
  format("% CHECKING.. ",[]),
  check_qu_ad_(Module, Q-QVN, A-AVN, LitQ),
  format("~s", [LitQ]).

% Answer-description AD (qua set-of-bindings) contains Answer.
contains(AD, Answer) :- append(Answer, _, AD).

?- contains(['Xs'=[C],'L'=1,'_A'=C,'_B'=D], ['Xs'=[A],'L'=1]).
   C = A.

?- check_qu_ad(quadtests, (?-length(_F,_G))-['Xs'=_F,'L'=_G],(_H=[],_I=0;_H=[_J],_I=1;_H=[_J,_K],_I=2;...)-['Xs'=_H,'L'=_I,'_A'=_J,'_B'=_K]).
% CHECKING.. (?-length(A,B)).
   _F = [_A,_B], _G = 2, _H = [_J,_K], _I = 2.

% Unravel the nested (;)/1 applications of multiple-AD structures.
unconj(Conj) --> { Conj = (Elt;Conj_) },
                 [Elt],
                 unconj(Conj_).
unconj(...) --> [].

?- phrase(unconj((_H=[],_I=0;_H=[_J],_I=1;_H=[_J,_K],_I=2;...)), List).
   List = [(_H=[],_I=0),(_H=[_J],_I=1),(_H=[_J,_K],_I=2)].

empty_anstack :-
    (   retract('$anstack'(_)), fail
    ;   asserta('$anstack'([]))
    ).

push(VN) :-
    retract('$anstack'(As)),
    asserta('$anstack'([VN|As])).

backtrack(N) :-
    (   '$anstack'(Ans),
        length(Ans, N) -> true
    ;   fail
    ).

n_answers(N, G, VN, ADs) :-
    must_be(integer, N),
    (   N > 0 -> n_answers_(N, G, VN, ADs)
    ;   domain_error(not_less_than_zero, N, n_answers/4)
    ).

n_answers_(N, G, VN, ADs) :-
    empty_anstack,
    call(G), push(VN),
    backtrack(N),
    !,
    retract('$anstack'(As)),
    reverse(As, ADs).

?- n_answers(3, length(Xs, L), ('Xs'=Xs,'Len'=L), ADs).
   Xs = [_A,_B], L = 2, ADs = [('Xs'=[],'Len'=0),('Xs'=[_C],'Len'=1),('Xs'=[_D,_E],'Len'=2)].
