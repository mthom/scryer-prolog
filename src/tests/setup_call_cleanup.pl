:- module(test_on_setup_call_cleanup, []).

:- use_module(library(iso_ext)).

test_queries_on_setup_call_cleanup :-
    \+ setup_call_cleanup(false, _, _),
    catch(setup_call_cleanup(true, throw(unthrown), _), error(instantiation_error, _), true),
    setup_call_cleanup(true, true, (true ; throw(x))),
    findall(X, setup_call_cleanup(true, X = 1, X = 2), [1]),
    findall(X, setup_call_cleanup(true, true, X = 2), [2]),
    findall(E, catch(setup_call_cleanup(true, X=true, X), error(E, _), true), [instantiation_error]),
    catch(setup_call_cleanup(X=throw(ex), true, X), ex, true),
    findall([S,G,C], setup_call_cleanup(S = 1, G = 2, C = 3), [[1,2,3]]),
    findall([S,G,C], setup_call_cleanup((S=1;S=2), G=3, C=4), [[1,3,4]]),
    findall([S,G], setup_call_cleanup(S=1, G=2, write_term(S+G, [variable_names(['S'=S,'G'=G])])), [[1,2]]),
    findall([S,G], setup_call_cleanup(S=1, (G=2;G=3), write_term(S+G, [variable_names(['S'=S,'G'=G])])), [[1,2],[1,3]]),
    findall([S,G], (setup_call_cleanup(S=1, G=2, write_term(S+G>A+B, [variable_names(['S'=S,'G'=G,'A'=A,'B'=B])])), A = 3, B = 4), [[1,2]]),
    findall([S,G,E], catch(setup_call_cleanup(S=1, (G=2;G=3,throw(x)), write_term(S+G, [variable_names(['S'=S,'G'=G])])), E, true), [[1,2,_],[_,_,x]]),
    findall([S,B,G], (setup_call_cleanup(S=1, (G=2;G=3),write_term(S+G>B, [variable_names(['S'=S,'G'=G,'B'=B])])), B=4, !), [[1,4,2]]),
    findall([S,G,B], (setup_call_cleanup(S=1,G=2,write_term(S+G>B, [variable_names(['S'=S,'G'=G,'B'=B])])),B=3,!), [[1,2,3]]),
    findall([S,G,B], (setup_call_cleanup(S=1,(G=2;false),write_term(S+G>B, [variable_names(['S'=S,'G'=G,'B'=B])])),B=3,!), [[1,2,3]]),
    findall([S,G,B], (setup_call_cleanup(S=1,(G=2;S=2),write_term(S+G>B, [variable_names(['S'=S,'G'=G,'B'=B])])), B=3, !), [[1,2,3]]),
    catch((setup_call_cleanup(S=1,(G=2;G=3), write_term(S+G>B, [variable_names(['S'=S,'G'=G,'B'=B])])), B=4, !, throw(x)), x, true),
    findall(Pat, catch(setup_call_cleanup(true,throw(goal),throw(cl)), Pat, true), [goal]),
    findall(Pat, catch(( setup_call_cleanup(true,(G=1;G=2),throw(cl)), throw(cont)), Pat, true), [cont]),
    findall([X,Y], (setup_call_cleanup(true, (X=1;X=2), writeq(a)), setup_call_cleanup(true,(Y=1;Y=2),writeq(b)), !), [[1,1]]).

:- initialization(test_queries_on_setup_call_cleanup).
