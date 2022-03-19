/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written 2022 by Adrián Arroyo Calle (adrian.arroyocalle@gmail.com)
   Part of Scryer Prolog.

   http_open(+Address, -Stream, +Options)
   ======================================

   Yields Stream to read the body of an HTTP reply from Address.
   Address is a list of characters, and includes the method. Both HTTP
   and HTTPS are supported.

   Example:

       ?- http_open("https://github.com/mthom/scryer-prolog", S, []).
       %@    S = '$stream'(0x7fcfc9e00f00).

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(http_open, [http_open/3]).

:- use_module(library(lists)).

http_open(Address, Response, Options) :-
    parse_http_options(Options, OptionValues),
    ( member(method(Method), OptionValues) -> true; Method = get),
    '$http_open'(Address, Response, Method).

parse_http_options(Options, OptionValues) :-
    maplist(parse_http_options_, Options, OptionValues).

parse_http_options_(method(Method), method(Method)) :-
    (  var(Method) ->
       throw(error(instantiation_error, http_open/3))
    ;
       lists:member(Method, [get, post, put, delete, patch, head]) -> true
    ;
       throw(error(domain_error(http_option, method(Method)), _))
    ).