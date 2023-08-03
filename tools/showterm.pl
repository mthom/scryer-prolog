/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Describe a term in GraphViz DOT format.
   Written September 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   Example:

      ?- dot(a+b).
      %@ graph G {
      %@     c [label = "(+)/2", fontname="courier bold"];
      %@     c -- c1;
      %@     c1 [label = "a", style=filled, fontname="courier bold", fillcolor=lightcyan];
      %@     c -- c2;
      %@     c2 [label = "b", style=filled, fontname="courier bold", fillcolor=lightcyan];
      %@ }
      %@    true.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- use_module(library(clpz)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(library(atts)).

:- attribute named/0.

dot :-
        read_term(Term, [variables(Vs),variable_names(NVs0)]),
        maplist(eq_pair, NVs0, NVPairs),
        pairs_values(NVPairs, NamedVariables),
        maplist(mark_var_as_named, NamedVariables),
        list_to_assoc(NVPairs, UsedNames),
        foldl(name_remaining_variables, Vs, NVs0-UsedNames, NVs-_),
        dot(Term, NVs).

eq_pair(A=B, A-B).

mark_var_as_named(Var) :-
        put_atts(Var, named).

name_remaining_variables(Var, NVs0-UsedNames0, NVs-UsedNames) :-
        (   get_atts(Var, named) ->
            NVs-UsedNames = NVs0-UsedNames0
        ;   unused_name(UsedNames0, 0, Name),
            NVs = [Name=Var|NVs0],
            put_assoc(Name, UsedNames0, Var, UsedNames)
        ).

unused_name(UsedNames, N0, Name) :-
        n_var_name(N0, Name0),
        (   get_assoc(Name0, UsedNames, _) ->
            N #= N0 + 1,
            unused_name(UsedNames, N, Name)
        ;   Name = Name0
        ).

n_var_name(N, VarName) :-
        char_code('A', AC),
        LN #= N mod 26 + AC,
        char_code(LC, LN),
        NN #= N // 26,
        zcompare(C, NN, 0),
        varname_(C, NN, LC, VarName).

varname_(=, _, LC, VarName) :-
        atom_chars(VarName, ['_', LC]).
varname_(>, NN, LC, VarName) :-
        number_chars(NN, NNChars),
        atom_chars(VarName, ['_', LC | NNChars]).


dot(Term) :-
        dot(Term, []).

dot(Term, NVs) :-
        phrase(term_labels(Term, NVs, c), Ls),
        phrase(("graph G {\n",
                dots(Ls),
                "}\n"), DOT),
        format("~s", [DOT]).

dots([]) --> [].
dots([D|Ds]) --> dot_(D), dots(Ds).

dot_(node_label(C, F, A)) -->
        format_("    ~w [label = \"~q\", fontname=\"courier bold\"];\n", [C,F/A]).
dot_(connection(A,B)) -->
        format_("    ~w -- ~w;\n", [A,B]).
dot_(atomic(C,L)) -->
        format_("    ~w [label = \"~q\", style=filled, fontname=\"courier bold\", fillcolor=lightcyan];\n", [C,L]).
dot_(variable(C,L)) -->
        format_("    ~w [label = \"~w\", shape=box, fontname=\"courier bold\", style=filled, fillcolor=aquamarine];\n", [C,L]).

term_labels(Term, NVs, C0) -->
        (   { atomic(Term) } -> [atomic(C0, Term)]
        ;   { var(Term) } ->
            (   { member(Name=Var, NVs), Var == Term } ->
                [variable(C0,Name)]
            ;   [variable(C0,Term)]
            )
        ;   { functor(Term, F, A),
              Term =.. [F|Args] },
            [node_label(C0, F, A)],
            all_subterms(Args, NVs, C0, 1)
        ).

all_subterms([], _, _, _) --> [].
all_subterms([L|Ls], NVs, C0, N0) -->
        [connection(C0, C1)],
        { phrase(format_("~w~w", [C0,N0]), Chars),
          atom_chars(C1, Chars),
          N #= N0 + 1 },
        term_labels(L, NVs, C1),
        all_subterms(Ls, NVs, C0, N).
