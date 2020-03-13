/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Written March 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   This library provides the nonterminal format_//2 to describe
   formatted strings. format/2 is provided for impure output.

   Usage:
   ======

   phrase(format_(FormatString, Arguments), Ls)

   format_//2 describes a list of characters Ls that are formatted
   according to FormatString. FormatString is a string (i.e.,
   a list of characters) that specifies the layout of Ls.
   The characters in FormatString are used literally, except
   for the following tokens with special meaning:

     ~w    use the next available argument from Arguments here,
           which must be atomic (a current limitation)
     ~f    use the next argument here, a floating point number
     ~Nf   where N is an integer: format the float argument
           using N digits after the decimal point
     ~s    use the next argument here, which must be a string
     ~N|   where N is an integer: place a tab stop at text column N
     ~N+   where N is an integer: place a tab stop N characters
           after the previous tab stop (or start of line)
     ~t    distribute spaces evenly between the two closest tab stops
     ~`Ct  like ~t, use character C instead of spaces to fill the space
     ~n    newline
     ~~    the literal ~

   The predicate format/2 is like format_//2, except that it outputs
   the text on the terminal instead of describing it declaratively.

   If at all possible, format_//2 should be used, to stress pure parts
   that enable easy testing etc. If necessary, you can emit the list Ls
   with maplist(write, Ls).

   The entire library only works if the Prolog flag double_quotes
   is set to chars, the default value in Scryer Prolog. This should
   also stay that way, to encourage a sensible environment.

   Example:

   ?- phrase(format_("~s~n~`.t~w!~12|", ["hello",there]), Cs).
   %@ Cs = [h,e,l,l,o,'\n','.','.','.','.','.','.',t,h,e,r,e,!] ;
   %@ false.

   I place this code in the public domain. Use it in any way you want.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(format, [format_//2,
                   format/2
                  ]).

:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(error)).

format_(Fs, Args) -->
        { must_be(list, Fs),
          must_be(list, Args),
          phrase(cells(Fs,Args,0,[]), Cells) },
        format_cells(Cells).

format_cells([]) --> [].
format_cells([Cell|Cells]) -->
        format_cell(Cell),
        format_cells(Cells).

format_cell(newline) --> "\n".
format_cell(cell(From,To,Es)) -->
        % distribute the space between the glue elements
        { phrase(elements_gluevars(Es, 0, Length), Vs),
          (   Vs = [] -> true
          ;   Space is To - From - Length,
              (   Space =< 0 -> maplist(=(0), Vs)
              ;   length(Vs, NumGlue),
                  Distr is Space // NumGlue,
                  Delta is Space - Distr*NumGlue,
                  (   Delta =:= 0 ->
                      maplist(=(Distr), Vs)
                  ;   BigGlue is Distr + Delta,
                      reverse(Vs, [BigGlue|Rest]),
                      maplist(=(Distr), Rest)
                  )
              )
          ) },
        format_elements(Es).

format_elements([]) --> [].
format_elements([E|Es]) -->
        format_element(E),
        format_elements(Es).

format_element(chars(Cs)) --> list(Cs).
format_element(glue(Fill,Num)) -->
        { length(Ls, Num),
          maplist(=(Fill), Ls) },
        list(Ls).

list([]) --> [].
list([L|Ls]) --> [L], list(Ls).

elements_gluevars([], N, N) --> [].
elements_gluevars([E|Es], N0, N) -->
        element_gluevar(E, N0, N1),
        elements_gluevars(Es, N1, N).

element_gluevar(chars(Cs), N0, N) -->
        { length(Cs, L),
          N is N0 + L }.
element_gluevar(glue(_,V), N, N) --> [V].

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Our key datastructure is a list of cells and newlines.
   A cell has the shape from_to(From,To,Elements), where
   From and To denote the positions of surrounding tab stops.

   Elements is a list of elements that occur in a cell,
   namely terms of the form chars(Cs) and glue(Char, Var).
   "glue" elements (TeX terminology) are evenly stretched
   to fill the remaining whitespace in the cell. For each
   glue element, the character Char is used for filling,
   and Var is a free variable that is used when the
   available space is distributed.

   newline is used if ~n occurs in a format string.
   It is is used because a newline character does not
   consume whitespace in the sense of format strings.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

cells([], _, Tab, Es) --> cell(Tab, Tab, Es).
cells([~,~|Fs], Args, Tab, Es) --> !,
        cells(Fs, Args, Tab, [chars("~")|Es]).
cells([~,w|Fs], [Arg|Args], Tab, Es) --> !,
        { arg_chars(Arg, Chars) },
        cells(Fs, Args, Tab, [chars(Chars)|Es]).
cells([~,n|Fs], Args, Tab, Es) --> !,
        cell(Tab, Tab, Es),
        [newline],
        cells(Fs, Args, 0, []).
cells([~,s|Fs], [Arg|Args], Tab, Es) --> !,
        cells(Fs, Args, Tab, [chars(Arg)|Es]).
cells([~,f|Fs], [Arg|Args], Tab, Es) --> !,
        { number_chars(Arg, Chars) },
        cells(Fs, Args, Tab, [chars(Chars)|Es]).
cells([~|Fs0], [Arg|Args], Tab, Es) -->
        { numeric_argument(Fs0, Num, [f|Fs]) },
        !,
        { number_chars(Arg, Cs0),
          phrase(upto_what(Bs, '.'), Cs0, Cs),
          (   Num =:= 0 -> Chars = Bs
          ;   (   Cs = ['.'|Rest] ->
                  length(Rest, L),
                  (   Num < L,
                      length(Ds, Num),
                      append(Ds, _, Rest)
                  ;   Num =:= L ->
                      Ds = Rest
                  ;   Num > L,
                      Delta is Num - L,
                      % we should look into the float with
                      % greater accuracy here, and use the
                      % actual digits instead of 0.
                      length(Zs, Delta),
                      maplist(=(0), Zs),
                      append(Rest, Zs, Ds)
                  )
              ;   length(Ds, Num),
                  maplist(=(0), Ds)
              ),
              append(Bs, ['.'|Ds], Chars)
          ) },
        cells(Fs, Args, Tab, [chars(Chars)|Es]).
cells([~,'`',Char,t|Fs], Args, Tab, Es) --> !,
        cells(Fs, Args, Tab, [glue(Char,_)|Es]).
cells([~,t|Fs], Args, Tab, Es) --> !,
        cells(Fs, Args, Tab, [glue(' ',_)|Es]).
cells([~|Fs0], Args, Tab, Es) -->
        { numeric_argument(Fs0, Num, ['|'|Fs]) },
        !,
        cell(Tab, Num, Es),
        cells(Fs, Args, Num, []).
cells([~|Fs0], Args, Tab0, Es) -->
        { numeric_argument(Fs0, Num, ['+'|Fs]) },
        !,
        { Tab is Tab0 + Num },
        cell(Tab0, Tab, Es),
        cells(Fs, Args, Tab, []).
cells([~,C|_], _, _, _) -->
        { atom_chars(A, [~,C]),
          domain_error(format_string, A) }.
cells([F|Fs0], Args, Tab, Es) -->
        { phrase(upto_what(Fs1, ~), [F|Fs0], Fs),
          Fs1 = [_|_] },
        cells(Fs, Args, Tab, [chars(Fs1)|Es]).

domain_error(Type, Term) :-
        throw(error(domain_error(Type, Term), _)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- phrase(upto_what(Cs, ~), "abc~test", Rest).
Cs = [a,b,c], Rest = [~,t,e,s,t].
?- phrase(upto_what(Cs, ~), "abc", Rest).
Cs = [a,b,c], Rest = [].
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

upto_what([], W), [W] --> [W], !.
upto_what([C|Cs], W) --> [C], !, upto_what(Cs, W).
upto_what([], _) --> [].


cell(From, To, Es0) -->
        (   { Es0 == [] } -> []
        ;   { reverse(Es0, Es) },
            [cell(From,To,Es)]
        ).

%?- numeric_argument("2f", Num, ['f'|Fs]).

%?- numeric_argument("100b", Num, Rs).

numeric_argument(Ds, Num, Rest) :-
        numeric_argument_(Ds, [], Ns, Rest),
        foldl(pow10, Ns, 0-0, Num-_).

numeric_argument_([D|Ds], Ns0, Ns, Rest) :-
        (   member(D, "0123456789") ->
            number_chars(N, [D]),
            numeric_argument_(Ds, [N|Ns0], Ns, Rest)
        ;   Ns = Ns0,
            Rest = [D|Ds]
        ).


pow10(D, N0-Pow0, N-Pow) :-
        N is N0 + D*10^Pow0,
        Pow is Pow0 + 1.


arg_chars(Arg, Chars) :-
        (   (   integer(Arg)
            ;   float(Arg)
            ) ->
            number_chars(Arg, Chars)
        ;   must_be(atom, Arg),
            atom_chars(Arg, Chars)
        ).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   Impure I/O, implemented as a small wrapper over format_//2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

format(Fs, Args) :-
        phrase(format_(Fs, Args), Cs),
        maplist(write, Cs).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
?- phrase(cells("hello", [], 0, []), Cs).

?- phrase(cells("hello~10|", [], 0, []), Cs).
?- phrase(cells("~ta~t~10|", [], 0, []), Cs).

?- phrase(format_("~`at~50|", []), Ls).

?- phrase(cells("~`at~50|", [], 0, []), Cs),
   phrase(format_cells(Cs), Ls).
?- phrase(cells("~ta~t~tb~tc~21|", [], 0, []), Cs).
Cs = [cell(0,21,[glue(' ',_38),chars([a]),glue(' ',_62),glue(' ',_67),chars([b]),glue(' ',_91),chars([c])])].
?- phrase(cells("~ta~t~4|", [], 0, []), Cs).
Cs = [cell(0,4,[glue(' ',_38),chars([a]),glue(' ',_62)])].

?- phrase(format_cell(cell(0,1,[glue(a,_94)])), Ls).

?- phrase(format_cell(cell(0,50,[chars("hello")])), Ls).

?- phrase(format_("~`at~50|~n", []), Ls).
?- phrase(format_("hello~n~tthere~6|", []), Ls).

?- format("~ta~t~4|", []).
 a  true ;
false.

?- format("~ta~tb~tc~10|", []).
  a  b   ctrue ;
false.

?- format("~tabc~3|", []).

?- format("~ta~t~4|", []).

?- format("~ta~t~tb~tc~20|", []).
    a         b    c
    a        b     ctrue ;
false.

?- format("~2f~n", [3]).
3.00
true ...

?- format("~20f", [0.1]).
0.10000000000000000000true ;   % this should use higher accuracy!
false.

?- X is atan(2), format("~7f~n", [X]).
1.1071487
X = 1.1071487177940906 ...

?- format("~`at~50|~n", []).
aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
true ...

?- format("~t~N", []).

- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
