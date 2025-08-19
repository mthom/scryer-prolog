:- module(warnings, []).

:- use_module(library(format)).
:- use_module(library(pio)).
:- use_module(library(lists)).

warn(Format, Vars) :-
    warn(user_error, Format, Vars).
warn(Stream, Format, Vars) :-
    prolog_load_context(file, File),
    prolog_load_context(term_position, position_and_lines_read(_,Line)),
    phrase_to_stream(
        (
            "% Warning: ", format_(Format,Vars), format_(" at line ~d of ~a~n",[Line,File])
        ),
        Stream
    ).

% FIXME: Replace with predicate_property(_, built_in) when #2600 will be ready
builtin((_;_)).
builtin((_,_)).
builtin((_->_)).
builtin(\+_).

unsound_type_test(atom(_)).
unsound_type_test(atomic(_)).
unsound_type_test(integer(_)).

:- meta_predicate maplistdif(3, ?, ?, ?).

maplistdif(_, [], [], L-L).
maplistdif(G__2, [H1|T1], [H2|T2], L0-LX) :-
    call(G__2, H1, H2, L0-L1),
    maplistdif(G__2, T1, T2, L1-LX).

%% arithmetic_expansion(+Type, ?Term, -ExpandedTerm, -Unifier-Rest).
%
% `ExpandedTerm` is the minimal generalization of `Term` which makes a valid
% arithmetic relation (`Type = rela`) or functional expression (`Type = func`).
% That means if all unifications from `Unifier` hold then `ExpandedTerm == Term`.
% `Unifier-Rest` form together a list difference. `Term` is traversed from left
% to right, depth-first. Given an invalid arithmetic term, as seen in the
% example below, `E` becomes valid arithmetic term, `L` - unifier:
%
% ```
% ?- arithmetic_expansion(rela, X is sqrt([]+Y*foo(e/2)), E, L-[]).
%    E = (X is sqrt(_A+Y*_B)), L = [[]=_A,foo(e/2)=_B].
% ```
%
% NOTE: Order of clauses is important for correctness.
arithmetic_expansion(func, T, T, L-L) :-
    (var(T); number(T)), !.
arithmetic_expansion(Set, T, R, LD) :-
    functor(T, F, A),
    arithmetic_term(Set, A, Fs),
    member(F, Fs), !,
    functor(R, F, A),
    T =.. [F|Ts],
    R =.. [F|Rs],
    maplistdif(arithmetic_expansion(func), Ts, Rs, LD).
arithmetic_expansion(func, T, R, [T=R|L]-L).

arithmetic_term(func, 0, [e,pi,epsilon]).
arithmetic_term(func, 1, [+,-,\,sqrt,exp,log,sin,cos,tan,asin,acos,atan,sign,abs,round,ceiling,floor,truncate,float,float_integer_part,float_fractional_part]).
arithmetic_term(func, 2, [+,-,/,*,**,^,/\,\/,xor,div,//,rdiv,<<,>>,mod,rem,max,min,gcd,atan2]).
arithmetic_term(rela, 2, [is,>,<,>=,=<,=:=,=\=]).

% Warn about builtin predicates re-definition. It can happen by mistake for
% example:
%     x :- a. b, c.
%
term_warning(term, Term, "(~q) attempts to re-define ~w", [Term,F/A]) :-
    builtin(Term),
    functor(Term, F, A).

% Warn about unsound type test predicates and suggest using library(si).
% Observe that following queries yield different results:
%
%     ?- X=1, integer(X).
%        true.
%     ?- integer(X), X=1.
%        false.
%
term_warning(goal, Term, "~q is a constant source of wrong results, use ~a_si/1 from library(si)", [F/1,F]) :-
    unsound_type_test(Term),
    functor(Term, F, 1).

% Warn when more than 2 negations are nested. Double negation has legit
% use-case, but I don't think that more nested negations are ever useful.
%
term_warning(goal, \+ \+ \+_, "Nested negations can be reduced", []).

% Warn about invalid arithmetic relation and show all incorrect sub-expression
term_warning(goal, Term, "Arithmetic expression ~w contains invalid terms ~q", [R, [H|T]]) :-
    arithmetic_expansion(rela, Term, R, [H|T]-[]).

%% expansion_hook(?Goal, +MetaVarSpecs).
%
% TLDR: Warn if currently expanded predicate calls one of its arguments, but it
% isn't declared as a meta-predicate.
%
% This hook is invoked just before goal expansion. `Goal` is an unexpanded
% goal, same as first argument of goal_expansion/2. `MetaVarSpecs` is a list of
% pairs of callable variables together with their qualifiers extracted from
% meta-predicate declaration of currently processed clause. In particular if it
% is an empty list then current head doesn't have any such variables: it is
% either not declared as a meta-predicate or its meta-predicate specification
% doesn't specify any callable variables (like `p(?)`).
%
% TODO: Be smarter and detect wrong meta-predicate declarations.
%
expansion_hook(Goal, []) :-
    % Detect if calling Goal leads to calling a free variable
    (   var(Goal) ->
        true
    ;   % Goal is a meta-predicate that calls free variable
        loader:module_expanded_head_variables(Goal, [_|_])
    ),
    warn("Meta-predicate detected, but no qualified variables found", []).

expansion_warning(ExpansionKind, Term) :-
    nonvar(Term),
    once(term_warning(ExpansionKind, Term, Msg, Vars)),
    warn(Msg, Vars),
    false.

user:term_expansion(Term, _) :-
    expansion_warning(term, Term).

user:goal_expansion(Term, _) :-
    expansion_warning(goal, Term).
