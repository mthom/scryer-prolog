:- module(http_server, [http_listen/2, sample_handler/2, sample_body_handler/2, parse_request/5]).

:- use_module(library(sockets)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(error)).
:- use_module(library(charsio)).
:- use_module(library(lists)).
:- use_module(library(iso_ext)).

% TODO
% - Parse body
% - Improve route matching
% - Long-running socket_server_accept
% - Cookies?
% - HTTP Error Codes
% - Redirections
% - Improve code quality
% - Binary
% - Comments
% - Test Suite
% - Keep-Alive
% - Case insensitive headers

http_listen(Port, Handlers) :-
    must_be(integer, Port),
    must_be(list, Handlers),
    once(socket_server_open(Port, Socket)),
    format("Listening at port ~d\n", [Port]),
    accept_loop(Socket, Handlers).

accept_loop(Socket, Handlers) :-
    setup_call_cleanup(socket_server_accept(Socket, Client, Stream, [type(binary)]),
        (
            read_header_lines(Stream, Lines),
            [Request|Headers] = Lines,
            (
                (phrase(parse_request(Version, Method, Path), Request), maplist(map_parse_header, Headers, HeadersKV)) -> (
                        (
                            member("Content-Length"-ContentLength, HeadersKV) ->
                                (number_chars(ContentLengthN, ContentLength), get_bytes(Stream, ContentLengthN, RequestBody))
                                ;true
                        ),
                        format("~w ~s\n", [Method, Path]),
                        call_handler(Path, HeadersKV, RequestBody, Handlers, Response),
                        http_response(StatusCode, ResponseBody, RequestHeaders) = Response,
                        format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
                        forall(member(RequestHeaderKey-RequestHeaderValue, RequestHeaders), format(Stream, "~s: ~s\r\n", [RequestHeaderKey, RequestHeaderValue])),
                        format(Stream, "\r\n~s", [ResponseBody])
                    );(
                        format(Stream, "HTTP/1.0 400 Bad Request\r\n\r\n", []) % bad format
                    )
            ),
            close(Stream)
        ), close(Stream)),
    accept_loop(Socket, Handlers).

call_handler(Path, Headers, _, Handlers, Response) :-
    member(get(Dcg, Handler), Handlers),
    phrase(Dcg, Path),!,
    Request = http_request(Headers, _),
    call(Handler, Request, Response).

call_handler(Path, Headers, Body, Handlers, Response) :-
    chars_utf8bytes(CharBody, Body),
    member(post(Dcg, Handler), Handlers),
    phrase(Dcg, Path),!,
    Request = http_request(Headers, CharBody),
    call(Handler, Request, Response).

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

map_parse_header(Header, HeaderKV) :-
    phrase(parse_header(HeaderKV), Header).

parse_header(Key-Value) -->
    string_without(":", Key),
    ": ",
    string_without("\r", Value),
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

get_bytes(Stream, Length, Res) :- get_bytes(Stream, Length, [], Res).
get_bytes(Stream, Length, Acc, Res) :-
  (Length > 0 -> (
    get_byte(Stream, B),
    B =\= -1,
    get_bytes(Stream, Length - 1, [B|Acc], Res)
  ); reverse(Acc, Res)).

sample_handler(http_request(Headers, _), Response) :-
    member("User-Agent"-UserAgent, Headers),
    Response = http_response(200, UserAgent, ["Content-Type"-"text/plain", "Connection"-"Close"]).

sample_body_handler(http_request(Headers, Body), http_response(200, Body, ["Content-Type"-"application/json"])).