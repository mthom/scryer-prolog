:- module(freeze, [freeze/2]).

:- use_module(library(atts)).

:- attribute frozen/1.

verify_attributes(Var, Other, Goals) :-
        get_atts(Var, frozen(Fa)), !,       % are we involved?
        (   var(Other) ->                   % must be attributed then
            (   get_atts(Other,  frozen(Fb)) % has a pending goal?
            ->  put_atts(Other, -frozen(Fb)),
	        put_atts(Other,  frozen((Fb,Fa))) % rescue conjunction
            ;   put_atts(Other,  frozen(Fa)) % rescue the pending goal
            ),
            Goals = []
        ;   Goals = [Fa]
        ).
verify_attributes(_, _, []).

freeze(X, Goal) :-
    put_atts(Fresh, frozen(Goal)),
    Fresh = X.

gather_freeze_goals(Attrs, _) :-
    var(Attrs), !.
gather_freeze_goals([frozen(X) | Attrs], [frozen(X) | Goals]) :-
    gather_freeze_goals(Attrs, Goals).
gather_freeze_goals([_ | Attrs], Goals) :-
    gather_freeze_goals(Attrs, Goals).

attribute_goals(X, Goals) :-
    '$get_attr_list'(X, Attrs),
    gather_freeze_goals(Attrs, Goals).
