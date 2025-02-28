:- module(http_open_hanging, [submit_request/0]).

:- use_module(library(charsio)).
:- use_module(library(http/http_open)).

send_request :-
    Options = [
        method('get'),
        status_code(StatusCode),
        request_headers([]),
        headers(_)
    ],
    http_open("https://scryer.pl", _Stream, Options),
    write_term('received response with status code':StatusCode, []), nl.

main :-
    send_request,
    send_request,
    send_request,
    send_request,
    send_request.

:- initialization(main).