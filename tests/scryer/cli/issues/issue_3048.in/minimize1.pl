:- use_module(library(format)).

% is_assoc copied from library(assoc) and renamed to is_assoc_
% and `% format("~w~n", [is_assoc_(R,RMin,Max,RDepth)]),` added

is_assoc_(Assoc) :-
    is_assoc_(Assoc, _Min, _Max, _Depth).

is_assoc_(t,X,X,0) :- !.
is_assoc_(t(K,_,-,t,t),K,K,1) :- !, ground(K).
is_assoc_(t(K,_,>,t,t(RK,_,-,t,t)),K,RK,2) :-
    % Ensure right side Key is 'greater' than K
    !, ground((K,RK)), K @< RK.

is_assoc_(t(K,_,<,t(LK,_,-,t,t),t),LK,K,2) :-
    % Ensure left side Key is 'less' than K
    !, ground((LK,K)), LK @< K.

is_assoc_(t(K,_,B,L,R),Min,Max,Depth) :-
    is_assoc_(L,Min,LMax,LDepth),
    % format("~w~n", [is_assoc_(R,RMin,Max,RDepth)]),
    is_assoc_(R,RMin,Max,RDepth),
    % Ensure Balance matches depth
    compare(Rel,RDepth,LDepth),
    balance(Rel,B),
    % Ensure ordering
    ground((LMax,K,RMin)),
    LMax @< K,
    K @< RMin,
    Depth is max(LDepth, RDepth)+1.

balance(=,-).
balance(>,>).
balance(<,<).

test :- is_assoc_(t(2,1,-,t(1,1,-,t,t),t(3,1,-,t,t))).

?- test.
   true.
