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

attribute_goals(Var) -->
    { get_atts(Var, frozen(Goals)) },
    [freeze(Var, Goals)].
