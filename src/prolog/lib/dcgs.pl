:- op(1200, xfx, -->).

:- module(dcgs, [phrase/2, phrase/3]).

:- use_module(library(lists), [append/3]).
:- use_module(library(terms)).

phrase(G, G) :-
    nonvar(G), G = [_|_], !.
phrase(G, Ls0) :-
    nonvar(G), G = (G1, G2), !, phrase(G1, Ls0, Ls1), phrase(G2, Ls1, []).
phrase(G, Ls0) :-
    call(G, Ls0, []).

phrase(G, Ls0, Ls1) :-
    nonvar(G), G = [_|_], !, append(G, Ls1, Ls0).
phrase(G, Ls0, Ls2) :-
    nonvar(G), G = (G1, G2), !,
    phrase(G1, Ls0, Ls1), phrase(G2, Ls1, Ls2).
phrase(G, Ls0, Ls1) :-
    call(G, Ls0, Ls1).

user:term_expansion(Term0, Term) :-
    numbervars(Term0, 0, N),
    expand_dcgs(Term0, N, Term).

expand_dcgs(Term0, N, (ModHead :- ModBody)) :-
    nonvar(Term0),
    Term0 = (Head, [SC | SCs] --> Body),
    !,
    nonvar(Head),
    Head =.. [RuleName | Args],
    append([SC | SCs], '$VAR'(N1), SemiContextArgs),
    append(Args, ['$VAR'(N), SemiContextArgs], ModArgs),
    ModHead =.. [RuleName | ModArgs],
    nonvar(Body),
    expand_body(Body, ModBody, N, N1).
expand_dcgs(Term0, N, (ModHead :- ModBody)) :-
    nonvar(Term0),
    Term0 = (Head --> Body),
    nonvar(Head),
    Head =.. [RuleName | Args],
    append(Args, ['$VAR'(N), '$VAR'(N1)], ModArgs),
    ModHead =.. [RuleName | ModArgs],
    nonvar(Body),
    expand_body(Body, ModBody, N, N1).

expand_body(Term0, ModTerms, N0, N) :-
    nonvar(Term0), Term0 = (Term, Terms), !,
    nonvar(Term),
    expand_body_term(Term, ModTerm, N0, N1),
    unfurl_commas(ModTerm, ModTerms, ModTerms1),
    expand_body(Terms, ModTerms1, N1, N).
expand_body(Term0, ModTerm, N0, N) :-
    nonvar(Term0),
    expand_body_term(Term0, ModTerm, N0, N).

/* unfurl_commas(?ModTerm, -ModTerms, -ModTerms1) :
   sets  ModTerms = (ModTermI0, ModTermI1, ..., ModTermIN, ModTerms1)
   where ModTerm  = (ModTermI0, ModTermI1, ..., ModTermIN) */
unfurl_commas(ModTerm, ModTerms, ModTerms1) :-
    nonvar(ModTerm),
    ModTerm  = (ModTermI0, ModTermIs),
    !,
    ModTerms = (ModTermI0, ModTerms2),
    unfurl_commas(ModTermIs, ModTerms2, ModTerms1).
unfurl_commas(ModTermIN, (ModTermIN, ModTerms1), ModTerms1).

expand_body_term([], true, N, N) :- !.
expand_body_term([Arg|Args], ModTerm, N0, N) :-
    !, N is N0 + 1,
    append([Arg|Args], '$VAR'(N), ModArgs),
    ModTerm = ('$VAR'(N0) = ModArgs).
expand_body_term((P -> Q), (PModTerm -> QModTerm), N0, N) :-
    !, expand_body(P, PModTerm, N0, N1),
    expand_body(Q, QModTerm, N1, N).
expand_body_term((P ; Q), (PModTerm ; QModTerm), N0, N) :-
    !, expand_body(P, PModTerm0, N0, N1),
    expand_body(Q, QModTerm0, N0, N2),
    ( N1 == N2 -> PModTerm = PModTerm0,
		  QModTerm = QModTerm0,
		  N = N1
    ; N1 < N2  -> unfurl_commas(PModTerm0, PModTerm, Hole),
		  Hole = ('$VAR'(N1) = '$VAR'(N2) ),
		  QModTerm = QModTerm0,
		  N = N2
    ; N1 > N2  -> unfurl_commas(QModTerm0, QModTerm, Hole),
		  Hole = ('$VAR'(N1) = '$VAR'(N2) ),
		  PModTerm = PModTerm0,
		  N = N1
    ).
expand_body_term(CommaTerm, ModTerm, N, N) :-
    CommaTerm =.. [{} | BodyTerms], !,
    comma_ify(BodyTerms, ModTerm).
expand_body_term(GrammarRule, ModTerm, N0, N) :-
    GrammarRule =.. [Name | Args],
    N is N0 + 1,
    append(Args, ['$VAR'(N0), '$VAR'(N)], ModArgs),
    ModTerm =.. [Name | ModArgs].

comma_ify([Term], Term) :- !.
comma_ify([Term | Args], (Term, Terms)) :-
    comma_ify(Args, Terms).
