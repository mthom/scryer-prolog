% Efforts toward literate tests with quads
 
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

:- use_module(testutils).
:- use_module(special_functions).

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

check_module_quads(Module, Quads) :-
    use_module(Module),
    read_quads(Module, Quads),
    zip(Qs, ADs, Quads),
    length(Qs, NQ),
    format("% Checking ~d quads ..~n", [NQ]),
    maplist(check_qu_ad, Qs, ADs).

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
check_qu_ad(Q-QVN, A-AVN) :-
    Q = ?-(G),
    phrase(portray_clause_(Q), LitQ), % NB: LitQ terminates w/ newline
    format("% CHECKING.. ",[]),
    (   A == true -> call(G)
    ;   A == false -> (   call(G) -> false
                      ;   true
                      )
    ;   phrase(unconj(A), As) ->
        (   length(As, N),
            n_answers(N, A, AVN, ADs),
            n_answers(N, G, QVN, Answers),
            maplist(contains, ADs, Answers)
        )
    ;   % Otherwise, we have the ',' case of a solitary answer
        call(G),
        call(A),
        QVN == AVN
    ),
    format("~s", [LitQ]).

% Answer-description AD (qua set-of-bindings) contains Answer.
contains(AD, Answer) :- append(Answer, _, AD).

?- contains(['Xs'=[C],'L'=1,'_A'=C,'_B'=D], ['Xs'=[A],'L'=1]).
   C = A.

?- check_qu_ad((?-length(_F,_G))-['Xs'=_F,'L'=_G],(_H=[],_I=0;_H=[_J],_I=1;_H=[_J,_K],_I=2;...)-['Xs'=_H,'L'=_I,'_A'=_J,'_B'=_K]).
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
