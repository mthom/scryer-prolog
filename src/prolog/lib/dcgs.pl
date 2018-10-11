:- module(dcgs, [(-->)/2, phrase/2, phrase/3]).

:- use_module(library(lists), [append/3]).

:- op(1200, xfx, -->).

phrase(G, Ls0) :-
    nonvar(G), G = [_|_], !, append(G, _, Ls0).
phrase(G, Ls0) :-
    nonvar(G), G = (G1, G2), !, phrase(G1, Ls0, Ls1), phrase(G2, Ls1).
phrase(G, Ls0) :-
    call(G, Ls0, []).

phrase(G, Ls0, Ls1) :-
    nonvar(G), G = [_|_], !, append(G, Ls1, Ls0).
phrase(G, Ls0, Ls2) :-
    nonvar(G), G = (G1, G2), !,
    phrase(G1, Ls0, Ls1), phrase(G2, Ls1, Ls2).
phrase(G, Ls0, Ls1) :-
    call(G, Ls0, Ls1).

term_expansion(Term0, (ModHead :- ModBody)) :-
    nonvar(Term0),
    Term0 = (Head, [SC | SCs] --> Body),
    !,
    nonvar(Head),
    Head =.. [RuleName | Args],
    append(Args, ['$VAR'(0), '$VAR'(N)], ModArgs), %% problematic line.
    ModHead =.. [RuleName | ModArgs],
    nonvar(Body),
    expand_body(Body, ModBody1, 0, N1),
    expand_body_term([SC | SCs], ModBody2, N1, N),
    ModBody = (ModBody1, ModBody2).
term_expansion(Term0, (ModHead :- ModBody)) :-
    nonvar(Term0),
    Term0 = (Head --> Body),
    nonvar(Head),
    Head =.. [RuleName | Args],
    append(Args, ['$VAR'(0), '$VAR'(N)], ModArgs),
    ModHead =.. [RuleName | ModArgs],
    nonvar(Body),
    expand_body(Body, ModBody, 0, N).

expand_body(Term0, (ModTerm, ModTerms), N0, N) :-
    nonvar(Term0), Term0 = (Term, Terms), !,
    expand_body_term(Term, ModTerm, N0, N1),
    expand_body(Terms, ModTerms, N1, N).
expand_body(Term0, ModTerm, N0, N) :-
    nonvar(Term0), expand_body_term(Term0, ModTerm, N0, N).

expand_body_term([], true, N, N) :- !.
expand_body_term([Arg|Args], ModTerm, N0, N) :-
    !, N is N0 + 1,
    append([Arg|Args], '$VAR'(N), ModArgs),
    ModTerm = ('$VAR'(N0) = ModArgs).
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
    comma_ify(Terms, Args).
