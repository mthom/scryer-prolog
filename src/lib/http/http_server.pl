:- module(http_server, [http_listen/2, sample_handler/1]).

:- use_module(library(sockets)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).

% TODO
% - Parse request Headers
% - Output response Headers
% - Improve route matching
% - Long-running socket_server_accept
% - Cookies?
% - HTTP Error Codes
% - Redirections
% - Improve code quality

http_listen(Port, Handlers) :-
    must_be(integer, Port),
    must_be(list, Handlers),
    once(socket_server_open(Port, Socket)),
    socket_server_accept(Socket, Client, Stream, [type(text)]),
    read_header_lines(Stream, Lines),
    [Request|Headers] = Lines,
    (
        phrase(parse_request(Version, Method, Path), Request) -> ( 
                call_handler(Path, Headers, Handlers, Response),
                http_response(StatusCode, Body) = Response,
                format(Stream, "HTTP/1.0 ~d\r\n\r\n~s", [StatusCode, Body])
            );(
                format(Stream, "HTTP/1.0 400 Bad Request\r\n\r\n", []) % bad format
            )
    ),
    close(Stream).

call_handler(Path, Headers, Handlers, Response) :-
    member(http_route(Dcg, Handler), Handlers),
    phrase(Dcg, Path),!,
    call(Handler, Response).

call_handler(_, _, _, http_response(404, "Not found")).

parse_request(http_version(Major, Minor), Method, Path) -->
    method(Method),
    " ",
    string_without(" ", Path),
    " ",
    "HTTP/",
    natural(Major),
    ".",
    natural(Minor),
    "\r\n".

method(options) --> "OPTIONS".
method(get) --> "GET".
method(head) --> "HEAD".
method(post) --> "POST".
method(put) --> "PUT".
method(delete) --> "DELETE".

string_without(Not, [Char|String]) -->
    [Char],
    {
        \+ member(Char, Not)
    },
    string_without(Not, String).

string_without(_, []) -->
    [].

natural(Nat) -->
    natural_(NatChars),
    {
        number_chars(Nat, NatChars)
    }.

natural_([Nat|Nats]) -->
    [Nat],
    {
        char_type(Nat, decimal_digit)
    },
    natural_(Nats).

natural_([]) -->
    [].

read_header_lines(Stream, Hs) :-
        read_line_to_chars(Stream, Cs, []),
        (   Cs == "" -> Hs = []
        ;   Cs == "\r\n" -> Hs = []
        ;   Hs = [Cs|Rest],
            read_header_lines(Stream, Rest)
        ).

sample_handler(Response) :-
    Response = http_response(200, "Hello Prolog friends!").