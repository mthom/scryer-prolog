:- module(http_server, [http_listen/2]).

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
                        ( call_handler(Path, HeadersKV, RequestBody, Handlers, Response) ->
                            send_response(Stream, Response)
                        ;   format(Stream, "HTTP/1.0 500 Internal Server Error\r\n\r\n", [])
                        )
                    );(
                        format(Stream, "HTTP/1.0 400 Bad Request\r\n\r\n", []) % bad format
                    )
            ),
            ! % Remove
        ), close(Stream)),
    accept_loop(Socket, Handlers).

call_handler(Path, Headers, _, Handlers, Response) :-
    member(get(Dcg, Handler), Handlers),
    phrase(Dcg, Path),!,
    Request = http_request(Headers, _),
    call(Handler, Request, Response).

call_handler(Path, Headers, Body, Handlers, Response) :-
    member(post(Dcg, Handler), Handlers),
    phrase(Dcg, Path),!,
    build_response(Body, ResponseBody),
    Request = http_request(Headers, ResponseBody),
    call(Handler, Request, Response).

call_handler(_, _, _, http_response(404, "Not found")).

build_response(ByteBody, text(TextBody)) :-
    chars_utf8bytes(TextBody, ByteBody).
build_response(ByteBody, binary(ByteBody)).

send_response(Stream, http_response(StatusCode, text(TextResponse), Headers)) :-
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("Content-Type"-"text/plain", Headers, Headers0),
    overwrite_header("Connection"-"Close", Headers0, Headers1),
    write_headers(Stream, Headers1),
    format(Stream, "\r\n~s", [TextResponse]).

send_response(Stream, http_response(StatusCode, binary(BinaryResponse), Headers)) :-
    format(Stream, "HTTP/1.0 ~d\r\n", [StatusCode]),
    overwrite_header("Connection"-"Close", Headers, Headers0),
    write_headers(Stream, Headers0),
    format(Stream, "\r\n", []),
    put_bytes(Stream, BinaryResponse).

write_headers(Stream, Headers) :-
    forall(member(Key-Value, Headers), format(Stream, "~s: ~s\r\n", [Key, Value])).

overwrite_header(Key-Value, [], [Key-Value]).
overwrite_header(Key-Value, [Header|Headers], HeadersOut) :-
    Header = Key0-_,
    Key0 \= Key,
    overwrite_header(Key-Value, Headers, HeadersOut).
overwrite_header(Key-Value, [Header|Headers], [NewHeader|Headers]) :-
    Header = Key-_,
    NewHeader = Key-Value.

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

put_bytes(_, []).
put_bytes(Stream, [Byte|Bytes]) :-
    put_byte(Stream, Byte),
    put_bytes(Stream, Bytes).