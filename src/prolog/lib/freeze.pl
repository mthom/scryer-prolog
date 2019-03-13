:- module(freeze, [freeze/2]).

:- use_module(library(atts)).

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

gather_freeze_goals(Attrs, _, _) :-
    var(Attrs), !.
gather_freeze_goals([frozen(X) | _], Var, [frozen(Var, X) | _]) :-
    !.
gather_freeze_goals([_ | Attrs], Var, Goals) :-
    gather_freeze_goals(Attrs, Var, Goals).

attribute_goals(X, Goals) :-
    '$get_attr_list'(X, Attrs),
    gather_freeze_goals(Attrs, X, Goals).
