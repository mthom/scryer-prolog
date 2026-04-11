:- use_module(library(process)).
:- use_module(library(http/http_server)).

server :-
    http_listen(8472, [get(/, hello)]).

hello(_Req, Res) :-
    http_body(Res, text("Ok")).