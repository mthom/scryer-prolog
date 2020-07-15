/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Predicates for parsing CSV data


  Read csv files

  Only two options with default values :
  - token_separator(',')
  - with_header(true)

  Examples

  * parsing a csv string:

  ?- use_module(library(csv)).
  ?- use_module(library(dcgs)).
  ?- phrase(parse_csv(Data), "col1,col2,col3,col4\none,2,,three").
    Data = frame(["col1","col2","col3","col4"],[["one",2,[],"three"]]).

  * with some options:

  ?- phrase(parse_csv(Data, [with_header(false), token_separator(';')]), "one;2;;three").
    Data = frame([],[["one",2,[],"three"]]).

  * parsing a csv file:

  ?- use_module(library(csv)).
  ?- use_module(library(pio)).
  ?- phrase_from_file(parse_csv(frame(Header, Rows)), './test.csv').


  Write csv files

  Four options with default values :
  - line_separator('\n')
  - token_separator(',')
  - with_header(true)
  - null_value(empty)

  Examples

  * writing a csv file:

  ?- use_module(library(csv)).
  ?- write_csv('./test.csv', frame(["col1","col2","col3","col4"], [["one",2,[],"three"]])).

  * with some options

  ?- use_module(library(csv)).
  ?- write_csv('./test.csv', frame(["col1","col2","col3","col4"], [["one",2,[],"three"]]), [with_header(false), line_separator('\r\n'), token_separator(';'), null_value('\\N')]).
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(csv, [
  parse_csv//1,
  parse_csv//2,
  write_csv/2,
  write_csv/3
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


%% -- write --


escaped_field([], []).
escaped_field(['"' | Y], ['"', '"' | R]) :-
  escaped_field(Y, R).
escaped_field([X | Y], [X | R]) :-
  X \== '"',
  escaped_field(Y, R).


ensure_escaped(Field, Field) :-
  (atom(Field); integer(Field); float(Field)).
ensure_escaped([X | Y], Field) :-
  escaped_field([X | Y], Field).


write_field(Field, Opt) :-
( Field \== [] ->
  ensure_escaped(Field, Field0),
  write(Field0)
  ; option(null_value(Null_Value), Opt),
    ( Null_Value == empty -> true
    ; write(Null_Value))).


write_row([Field], Opt) :-
  write_field(Field, Opt).
write_row([Field, X | Y], Opt) :-
  write_field(Field, Opt),
  option(token_separator(Tk_Sep), Opt),
  write(Tk_Sep),
  write_row([X | Y], Opt).


write_rows([Row], Opt) :-
  write_row(Row, Opt).
write_rows([Row, X | Y], Opt) :-
  option(line_separator(Line_Sep), Opt),
  write_row(Row, Opt),
  write(Line_Sep),
  write_rows([X | Y], Opt).


write_csv(File_Name, frame(Header, Rows), Opt) :-
  option_extends(Opt, [
    null_value(empty),
    token_separator(','),
    with_header(true),
    line_separator('\n')
  ], Opt0),
  open(File_Name, write, Out),
  set_output(Out),
  option(with_header(With_Header), Opt0),
  ( With_Header == true -> 
    write_row(Header, Opt0),
    option(line_separator(Line_Sep), Opt0),
    write(Line_Sep)
  ; true),
  write_rows(Rows, Opt0),
  close(Out),
  set_output(user_output).
write_csv(File_Name, Frm) :-
  write_csv(File_Name, Frm, []).


%% -- read --


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
      with_header(true),
      token_separator(',')
    ], Opt0)
  },
  ( { option(with_header(With_Header), Opt0),
      With_Header == true } ->
    row(Header, Opt0),
    { Header \== [[]] },
    end_token
  ; { Header = [] }),
  rows(Rows, Opt0).
parse_csv(R) -->
  parse_csv(R, []).
