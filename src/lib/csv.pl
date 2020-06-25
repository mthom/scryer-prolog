/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Predicates for parsing CSV data

  Only two options are provided with default values :
  - token_separator(',') 
  - skip_header(false)

  Examples

  * parsing a csv string:

  ?- use_module(library(csv)).
  ?- use_module(library(dcgs)).
  ?- phrase(parse_csv(Data), "col1,col2,col3,col4\none,2,,three").
    Data = frame(["col1","col2","col3","col4"],[["one",2,[],"three"]]).

  * with some options:

  ?- phrase(parse_csv(Data, [skip_header(true),token_separator(';')]), "col1;col2;col3,col4\none;2;;three").
    Data = frame([],[["one",2,[],"three"]]).

  * parsing a csv file:

  ?- use_module(library(csv)).
  ?- use_module(library(pio)).
  ?- phrase_from_file(parse_csv(frame(Header, Rows)), './test.csv').
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(csv, [
  parse_csv//1,
  parse_csv//2
]).

:- use_module(library(dcgs)).
:- use_module(library(lists)).


option(W, O) :-
  ( member(W, O) -> true
  ; throw(not_found_error(W, O))).


option_extends([], Opt, Opt).
option_extends([X | Y], Opt0, Opt) :-
  functor(X, Name, 1),
  F0 =.. [Name, _],
  ( select(F0, Opt0, R) ->
    option_extends(Y, [X | R], Opt)
  ; option_extends(Y, [X | Opt0], Opt) ).



tokens([], Opt), [Tk_Sep] -->
  { option(token_separator(Tk_Sep), Opt) },
  [Tk_Sep],
  !.
tokens([], _), "\r\n" -->
  "\r\n",
  !.
tokens([], _), "\n" -->
  "\n",
  !.
tokens([], _), "\r" -->
  "\r",
  !.
tokens([X | Y], Opt) -->
  [X],
  !,
  tokens(Y, Opt).
tokens([], _) --> [].


field(R, Opt) -->
  "\"",
  !,
  string_tokens(R, Opt).
field(R, Opt) -->
  tokens(R0, Opt),
  { R0 \== [],
    catch(number_chars(R, R0), _, R = R0)
  }.
field([], _) --> [].


string_tokens(R, Opt) -->
  [X],
  ( { X == '"' } ->
    ( "\"" ->
      { R = [X | Y] },
      string_tokens(Y, Opt)
    ; { R = [] })
  ; { R = [X | Y] },
    string_tokens(Y, Opt)).


end_token --> "\r\n".
end_token --> "\n".
end_token --> "\r".
end_token --> [].


separator(Opt) -->
    { option(token_separator(Tk_Sep), Opt) },
    [Tk_Sep].


row([X | Y], Opt) -->
  field(X, Opt),
  !,
  ( separator(Opt) ->
    row(Y, Opt)
  ; end_token ->
    { Y = [] }).


rows(R, Opt) -->
  row(X, Opt),
  !,
  ( { X \== [[]] } ->
    rows(Y, Opt),
    { R = [X | Y] }
  ; { R = [] }).


parse_csv(frame(Header, Rows), Opt) --> 
  { option_extends(Opt, [
      skip_header(false),
      token_separator(',')
    ], Opt0)
  },
  ( { member(skip_header(false), Opt0) } ->
    row(Header, Opt0),
    { Header \== [[]] },
    end_token
  ; row(_, Opt0),
    end_token,
    { Header = [] }),
  rows(Rows, Opt0).
parse_csv(R) -->
  parse_csv(R, []).
