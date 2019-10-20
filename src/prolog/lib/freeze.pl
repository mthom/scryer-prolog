:- module(freeze, [freeze/2]).

:- use_module(library(atts)).
:- use_module(library(dcgs)).

:- attribute frozen/1.

verify_attributes(Var, Other, Goals) :-
        get_atts(Var, frozen(Fa)), !,       % are we involved?
        (   var(Other) ->                   % must be attributed then
            (   get_atts(Other,  frozen(Fb)) % has a pending goal?
            ->  put_atts(Other,  frozen((Fb,Fa))) % rescue conjunction
            ;   put_atts(Other,  frozen(Fa)) % rescue the pending goal
            ),
            Goals = []
        ;   Goals = [Fa]
        ).
verify_attributes(_, _, []).

freeze(X, Goal) :-
    put_atts(Fresh, frozen(Goal)),
    Fresh = X.

gather_freeze_goals(Attrs, _) -->
    { var(Attrs) },
    !.
gather_freeze_goals([frozen(X) | _], Var) -->
    [freeze(Var, X)],
    { put_atts(Var, -frozen(_)) },
    !.
gather_freeze_goals([_ | Attrs], Var) -->
    gather_freeze_goals(Attrs, Var).

attribute_goals(X) -->
    { '$get_attr_list'(X, Attrs) },
    gather_freeze_goals(Attrs, X).
