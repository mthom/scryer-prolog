/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written in December 2020 by Adrián Arroyo (adrian.arroyocalle@gmail.com)
   Updated in March 2022 by Adrián Arroyo to use the Hyper backend
   Part of Scryer Prolog.
   I place this code in the public domain. Use it in any way you want.
*/

/** This library provides an starting point to build HTTP server based applications.
It is based on [Warp](https://github.com/seanmonstar/warp), which allows for HTTP/1.0, HTTP/1.1 and HTTP/2. However,
some advanced features that Warp provides are still not accesible.

## Usage

The main predicate of the library is `http_listen/2`, which needs a port number
(usually 80) and a list of handlers. A handler is a compound term with the functor
as one HTTP method (in lowercase) and followed by a Route Match and a predicate
which will handle the call.

```
text_handler(Request, Response) :-
  http_status_code(Response, 200),
  http_body(Response, text("Welcome to Scryer Prolog!")).

parameter_handler(User, Request, Response) :-
  http_body(Response, text(User)).

http_listen(7890, [
  get(echo, text_handler),                 % GET /echo
  post(user/User, parameter_handler(User)) % POST /user/<User>
]).
```

Every handler predicate will have at least 2-arity, with Request and Response.
Although you can work directly with `http_request` and `http_response` terms, it is
recommeded to use the helper predicates, which are easier to understand and cleaner:

   - `http_headers(Response/Request, Headers)`
   - `http_status_code(Responde, StatusCode)`
   - `http_body(Response/Request, text(Body))`
   - `http_body(Response/Request, binary(Body))`
   - `http_body(Request, form(Form))`
   - `http_body(Response, file(Filename))`
   - `http_redirect(Response, Url)`
   - `http_query(Request, QueryName, QueryValue)`

Some things that are still missing:

   - Read forms in multipart format
   - Session handling via cookies
   - HTML Templating (but you can use [Teruel](https://github.com/aarroyoc/teruel/), [Marquete](https://github.com/aarroyoc/marquete/) or [Djota](https://github.com/aarroyoc/djota) for that)
*/


:- module(http_server, [
	      http_listen/2,
	      http_listen/3,
	      http_headers/2,
	      http_status_code/2,
	      http_body/2,
	      http_redirect/2,
	      http_query/3,
	      http_basic_auth/4
]).

:- meta_predicate http_listen(?, :).
:- meta_predicate http_listen(?, :, ?).

:- meta_predicate http_basic_auth(:, :, ?, ?).

:- use_module(library(charsio)).
:- use_module(library(crypto)).
:- use_module(library(error)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(lists)).
:- use_module(library(pio)).
:- use_module(library(time)).

%% http_listen(+Port, +Handlers).
%
% Equivalent to `http_listen(Port, Handlers, [])`.
http_listen(Port, Module:Handlers0) :-
    must_be(integer, Port),
    must_be(list, Handlers0),
    maplist(module_qualification(Module), Handlers0, Handlers),
    http_listen_(Port, Handlers, []).

%% http_listen(+Port, +Handlers, +Options).
%
% Listens for HTTP connections on port Port. Each handler on the list Handlers should be of the form: `HttpVerb(PathUnification, Predicate)`.
% For example: `get(user/User, get_info(User))` will match an HTTP request that is a GET, the path unifies with /user/User (where User is a variable)
% and it will call `get_info` with three arguments: an `http_request` term, an `http_response` term and User.
%
% The following options are supported:
%
% - `tls_key(+Key)` - a TLS key for HTTPS (string)
% - `tls_cert(+Cert)` - a TLS cert for HTTPS (string)
% - `content_length_limit(+Limit)` - maximum length (in bytes) for the incoming bodies. By default, 32KB.
%
% In order to have a HTTPS server (instead of plain HTTP), both `tls_key` and `tls_cert` options must be provided.
http_listen(Port, Module:Handlers0, Options) :-
    must_be(integer, Port),
    must_be(list, Handlers0),
    must_be(list, Options),
    maplist(module_qualification(Module), Handlers0, Handlers),
    http_listen_(Port, Handlers, Options).

module_qualification(M, H0, H) :-
    H0 =.. [Method, Path, Goal],
    H =.. [Method, Path, M:Goal].

http_listen_(Port, Handlers, Options) :-
    parse_options(Options, TLSKey, TLSCert, ContentLengthLimit),
    phrase(format_("0.0.0.0:~d", [Port]), Addr),
    '$http_listen'(Addr, HttpListener, TLSKey, TLSCert, ContentLengthLimit),!,
    format("Listening at ~s\n", [Addr]),
    http_loop(HttpListener, Handlers).

parse_options(Options, TLSKey, TLSCert, ContentLengthLimit) :-
    member_option_default(tls_key, Options, "", TLSKey),
    member_option_default(tls_cert, Options, "", TLSCert),
    member_option_default(content_length_limit, Options, 32768, ContentLengthLimit),
    must_be(integer, ContentLengthLimit).

member_option_default(Key, List, _Default, Value) :-
    X =.. [Key, Value],
    member(X, List).
member_option_default(Key, List, Default, Default) :-
    X =.. [Key, _],
    \+ member(X, List).
	

http_loop(HttpListener, Handlers) :-
    '$http_accept'(HttpListener, RequestMethod, RequestPath, RequestHeaders, RequestQuery, RequestStream, ResponseHandle),
    current_time(Time),
    phrase(format_time("%Y-%m-%d (%H:%M:%S)", Time), TimeString),
    format("~s ~w ~s\n", [TimeString, RequestMethod, RequestPath]),
    maplist(map_header_kv, RequestHeaders, RequestHeadersKV),
    phrase(parse_queries(RequestQueries), RequestQuery),
    (
	match_handler(Handlers, RequestMethod, RequestPath, Handler) ->
	(
	    HttpRequest = http_request(RequestHeadersKV, stream(RequestStream), RequestQueries),
	    HttpResponse = http_response(_, _, _),
	    (call(Handler, HttpRequest, HttpResponse) ->
		 send_response(ResponseHandle, HttpResponse)
	    ;    (
		'$http_answer'(ResponseHandle, 500, [], ResponseStream),
		call_cleanup(format(ResponseStream, "Internal Server Error", []), close(ResponseStream)))
	    )
	)
    ; (
	'$http_answer'(ResponseHandle, 404, [], ResponseStream),
	call_cleanup(format(ResponseStream, "Not Found", []), close(ResponseStream)))
    ),
    http_loop(HttpListener, Handlers).

send_response(ResponseHandle, http_response(StatusCode0, text(ResponseText), ResponseHeaders0)) :-
    default(StatusCode0, 200, StatusCode),
    maplist(map_header_kv_2, ResponseHeaders, ResponseHeaders0),
    '$http_answer'(ResponseHandle, StatusCode, ResponseHeaders, ResponseStream0),
    open(stream(ResponseStream0), write, ResponseStream, [type(text)]),
    catch(
	call_cleanup(format(ResponseStream, "~s", [ResponseText]),close(ResponseStream)),
	error(existence_error(stream, _), _),
	true
    ).

send_response(ResponseHandle, http_response(StatusCode0, bytes(ResponseBytes), ResponseHeaders0)) :-
    default(StatusCode0, 200, StatusCode),
    maplist(map_header_kv_2, ResponseHeaders, ResponseHeaders0),
    '$http_answer'(ResponseHandle, StatusCode, ResponseHeaders, ResponseStream),
    catch(
        call_cleanup(format(ResponseStream, "~s", [ResponseBytes]),close(ResponseStream)),
	error(existence_error(stream, _), _),
	true
    ).

send_response(ResponseHandle, http_response(StatusCode0, file(Filename), ResponseHeaders0)) :-
    default(StatusCode0, 200, StatusCode),
    maplist(map_header_kv_2, ResponseHeaders, ResponseHeaders0),
    '$http_answer'(ResponseHandle, StatusCode, ResponseHeaders, ResponseStream),
    catch(
	call_cleanup(
	    setup_call_cleanup(
		open(Filename, read, FileStream, [type(binary)]),
		(
		    get_n_chars(FileStream, _, FileCs),
		    format(ResponseStream, "~s", [FileCs])
		),
		close(FileStream)
	    ),
	    close(ResponseStream)
	),
	error(existence_error(stream, _), _),
	true
    ).


default(Var, Default, Out) :-
    (var(Var) -> Out = Default
    ;   Var = Out  
    ).

map_header_kv(T, K-V) :-
    T =.. [K0, V],
    atom_chars(K0, K).

map_header_kv_2(T, K-V) :-
    atom_chars(K0, K),
    T =.. [K0, V].

match_handler(Handlers, Method, "/", Handler) :-
    member(H, Handlers),
    H =.. [Method, /, Handler].
match_handler(Handlers, Method, Path, Handler) :-
    member(H, Handlers),
    copy_term(H, H1),
    H1 =.. [Method, Pattern, Handler],
    \+ var(Pattern),
    phrase(path(Pattern), Path).
match_handler(Handlers, Method, Path, Handler) :-
    member(H, Handlers),
    copy_term(H, H1),
    H1 =.. [Method, Var, Handler],
    var(Var),
    Var = Path.

path(Pattern) -->
    {
        Pattern =.. Parts,
        length(Parts, 3),
        nth0(1, Parts, Pattern0),
        nth0(2, Parts, PartAtom),
        (var(PartAtom) -> Part = PartAtom; atom_chars(PartAtom, Part))
    },
    path(Pattern0),
    "/",
    string_without("/", Part).

path(Pattern) -->
    {
        Pattern =.. Parts,
        Parts = [PartAtom],
        (var(PartAtom) -> Part = PartAtom; atom_chars(PartAtom, Part))
    },
    "/",
    string_without("/", Part).

path([]) --> [].

string_without(Not, [Char|String]) -->
    [Char],
    {
        \+ member(Char, Not)
    },
    string_without(Not, String).

string_without(_, []) -->
    [].

%% http_headers(?Request_Response, ?Headers).
%
% True iff `Request_Response` is a request or response with headers Headers. Can be used both to get headers (usually in from a request)
% and to add headers (usually in a response).
http_headers(http_request(Headers, _, _), Headers).
http_headers(http_response(_, _, Headers), Headers).

%% http_body(?Request_Response, ?Body).
%
% True iff Body is the body of the request or response. A body can be of the following types:
%
%  * `bytes(Bytes)` for both requests and responses, interprets the body as bytes
%  * `text(Bytes)` for both requests and responses, interprets the body as text
%  * `form(Form)` only for requests, interprets the body as an `application/x-www-form-urlencoded` form.
%  * `file(File)` only for responses, interprets the body as the content of a file (useful to send static files).
http_body(http_request(_, stream(StreamBody), _), bytes(BytesBody)) :- get_n_chars(StreamBody, _, BytesBody).
http_body(http_request(_, stream(StreamBody), _), text(TextBody)) :- get_n_chars(StreamBody, _, TextBody).
http_body(http_request(Headers, stream(StreamBody), _), form(FormBody)) :- 
    member("content-type"-"application/x-www-form-urlencoded", Headers),
    get_n_chars(StreamBody, _, TextBody),
    phrase(parse_queries(FormBody), TextBody).
http_body(http_request(_, Body, _), Body).
http_body(http_response(_, Body, _), Body).

%% http_status_code(?Response, ?StatusCode).
%
% True iff the status code of the response Response unifies with StatusCode.
http_status_code(http_response(StatusCode, _, _), StatusCode).

%% http_redirect(-Response, +Uri).
%
% True iff Response is a response that redirects the user to the uri Uri.
http_redirect(http_response(307, text("Moved Temporarily"), ["Location"-Uri]), Uri).

%% http_query(+Request, ?Key, ?Value).
%
% True iff there's a query in request Request with key Key and value Value.
http_query(http_request(_, _, Queries), Key, Value) :- member(Key-Value, Queries).

parse_queries([Key-Value|Queries]) -->
    string_without("=", Key0),
    "=",
    string_without("&", Value0),
    "&",
    parse_queries(Queries),
    {
	phrase(url_decode(Key), Key0),
	phrase(url_decode(Value), Value0)
    }.

parse_queries([Key-Value]) -->
    string_without("=", Key0),
    "=",
    string_without(" ", Value0),
    {
	phrase(url_decode(Key), Key0),
        phrase(url_decode(Value), Value0)  
    }.

parse_queries([]) -->
    [].

% Decodes a UTF-8 URL Encoded string: RFC-1738
url_decode([Char|Chars]) -->
    [Char],
    {
        Char \= '%',
	Char \= (+)
    },
    url_decode(Chars).
url_decode([' '|Chars]) -->
    "+",
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A],
    [B],
    {
        hex_bytes([A,B], Bytes),
        Bytes = [FirstByte|_],
        FirstByte < 128,
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A, B],
    "%",
    [C, D],
    {
        hex_bytes([A,B,C,D], Bytes),
        Bytes = [FirstByte|_],
        FirstByte < 224,
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A, B],
    "%",
    [C, D],
    "%",
    [E, F],
    {
        hex_bytes([A,B,C,D,E,F], Bytes),
        Bytes = [FirstByte|_],
        FirstByte < 240,
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).
url_decode([Char|Chars]) -->
    "%",
    [A, B],
    "%",
    [C, D],
    "%",
    [E, F],
    "%",
    [H, I],
    {
        hex_bytes([A,B,C,D,E,F,H,I], Bytes),
        chars_utf8bytes(Chars0, Bytes),
        Chars0 = [Char]
    },
    url_decode(Chars).

url_decode([]) --> [].

%% http_basic_auth(+LoginPredicate, +Handler, +Request, -Response)
%
% Metapredicate that wraps an existing Handler with an HTTP Basic Auth flow.
% Checks if a given user + password is authorized to execute that handler, returning 401
% if it's not satisfied.
% 
% `LoginPredicate` must be a predicate of arity 2 that takes a User and a Password.
% `Handler` will have, in addition to the Request and Response arguments, a User argument
% containing the User given in the authentication.
%
% Example:
%
% ```
% main :-
%    http_listen(8800,[get('/', http_basic_auth(login, inside_handler("data")))]).
%
% login(User, Pass) :-
%    User = "aarroyoc",
%    Pass = "123456".
%
% inside_handler(Data, User, Request, Response) :-
%    http_body(Response, text(User)).
% ```
http_basic_auth(LoginPredicate, Handler, Request, Response) :-
    http_headers(Request, Headers),
    member("authorization"-AuthorizationStr, Headers),
    append("Basic ", Coded, AuthorizationStr),
    chars_base64(UserPass, Coded, []),
    append(User, [':'|Password], UserPass),
    (
	call(LoginPredicate, User, Password) ->
	call(Handler, User, Request, Response)
    ;   http_basic_auth_unauthorized_response(Response)
    ).

http_basic_auth(_LoginPredicate, _Handler, Request, Response) :-
    http_headers(Request, Headers),
    \+ member("authorization"-_, Headers),
    http_basic_auth_unauthorized_response(Response).

http_basic_auth_unauthorized_response(Response) :-
    http_status_code(Response, 401),
    http_headers(Response, ["www-authenticate"-"Basic realm=\"Scryer Prolog\", charset=\"UTF-8\""]),
    http_body(Response, text("Unauthorized")).
	
