/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
   The original copyright and licence information is shown below.

   Adapted in June 2020 by Markus Triska (triska@metalevel.at)
   Part of Scryer Prolog.

   In order to improve portability and reliability of this library, I
   have changed various parts of the original code to make it
   conforming to the Prolog ISO standard. I have removed all
   occurrences of proprietary non-standard ad hoc data types.

   In Scryer Prolog, we represent strings as lists of characters.
   This makes them amenable to processing with DCGs and other
   built-in mechanisms such as existing predicates on lists.
   Scryer Prolog represents lists of characters very compactly,
   making it an ideal representation for large amounts of text. It
   fully conforms to the ISO standard and is very portable.

   This library is intended to be used in tandem with load_html/3
   from library(sgml), which creates DOM trees from markup documents.
   It can be combined with http_open/3 from library(http/http_open)
   to read such documents directly from network connections.

   For instance, to inspect all links to Prolog files (*.pl) on
   Scryer Prolog's project page, we can use:

      :- use_module(library(http/http_open)).
      :- use_module(library(sgml)).
      :- use_module(library(xpath)).
      :- use_module(library(dcgs)).

      link_to_pl_file(File) :-
          http_open("https://github.com/mthom/scryer-prolog", S, []),
          load_html(stream(S), DOM, []),
          xpath(DOM, //a(@href), File),
          phrase((...,".pl"), File).

   Yielding:

      ?- link_to_pl_file(File).
      %@    File = "/mthom/scryer-prolog/blob/master/src/lib/dcgs.pl"
      %@ ;  File = "/mthom/scryer-prolog/blob/master/src/lib/pio.pl"
      %@ ;  File = "/mthom/scryer-prolog/blob/master/src/lib/tabling.pl"
      %@ ;  ... .

   Parts of the original functionality may not yet work. Please
   consider such parts opportunities for improvements, and file
   issues in case you need additional features.

   The original copyright information follows.

   ======================================================================


    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2009-2019, University of Amsterdam
                              VU University Amsterdam
                              CWI, Amsterdam
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

:- module(xpath,
          [ xpath/3,                    % +DOM, +Spec, -Value
            xpath_chk/3,                % +DOM, +Spec, -Value

            op(400, fx, //),
            op(400, fx, /),
            op(200, fy, @)
          ]).

:- use_module(library(lists),[member/2,memberchk/2,reverse/2]).
:- use_module(library(charsio)).
:- use_module(library(error)).
:- use_module(library(dcgs)).
:- use_module(library(si)).

/** Select nodes in an XML DOM

The library xpath.pl provides predicates to select nodes from an XML DOM
tree as produced by `library(sgml)` based  on descriptions inspired by the
[XPath language](http://www.w3.org/TR/xpath).

The   predicate   `xpath/3`   selects   a   sub-structure   of   the   DOM
non-deterministically based on an  XPath-like   specification.  Not  all
selectors of XPath are implemented, but the ability to mix `xpath/3` calls
with arbitrary Prolog code  provides  a   powerful  tool  for extracting
information from XML parse-trees.
*/

element_name(element(Name,_,_), Name).
element_attributes(element(_,Attributes,_), Attributes).
element_content(element(_,_,Content), Content).

%% xpath_chk(+DOM, +Spec, ?Content) is semidet.
%
% Semi-deterministic version of `xpath/3`.

xpath_chk(DOM, Spec, Content) :-
    xpath(DOM, Spec, Content),
    !.

%% xpath(+DOM, +Spec, ?Content) is nondet.
%
% Match an element in a DOM structure.   The syntax is inspired by
% XPath, using () rather than  []   to  select  inside an element.
% First we can construct paths using / and //:
%
% - *//Term*
%   Select any node in the DOM matching term.
%
% - */Term*
%   Match the root against Term.
%
% - *Term*
%   Select the immediate children of the root matching Term.
%
% The Terms above are of type   _callable_.  The functor specifies
% the element name. The element name   `*`  refers to any element.
% The name _self_ refers to the   top-element  itself and is often
% used for processing matches of an  earlier `xpath/3` query. A term
% NS:Term refers to an XML  name   in  the  namespace NS. Optional
% arguments specify additional  constraints   and  functions.  The
% arguments are processed from left  to right. Defined conditional
% argument values are:
%
% - *`index(?Index)`*
%   True if the element is the Index-th child of its parent,
%   where 1 denotes the first child. Index can be one of:
%
%  - *`Var`*
%    `Var` is unified with the index of the matched element.
%  - *`last`*
%    True for the last element.
%  - *`last - IntExpr`*
%    True for the last-minus-nth element. For example,
%    `last-1` is the element directly preceding the last one.
%  - *`IntExpr`*
%    True for the element whose index equals `IntExpr`.
% - *`Integer`*
%   The N-th element with the given name, with 1 denoting the
%   first element. Same as `index(Integer)`.
% - *`last`*
%   The last element with the given name. Same as
%   `index(last)`.
% - *`last - IntExpr`*
%   The IntExpr-th element before the last.
%   Same as `index(last-IntExpr)`.
%
% Defined function argument values are:
%
% - *`self`*
%   Evaluate to the entire element
% - *`content`*
%   Evaluate to the content of the element (a list)
% - *`text`*
%   Evaluates to all text from the sub-tree, represented
%   as a list of characters.
% - *`text(atom)`*
%   Evaluates to all text from the sub-tree as an atom.
% - *`normalize_space`*
%   As `text`, but uses `normalize_space/2` to normalise
%   white-space in the output
% - *`number`*
%   Extract an integer or float from the value.  Ignores
%   leading and trailing white-space
% - *`@Attribute`*
%   Evaluates to the value of the given attribute.  Attribute
%   can be a compound term. In this case the functor name
%   denotes the element and arguments perform transformations
%   on the attribute value.  Defined transformations are:
%
%   - *`number`*
%     Translate the value into a number using
%     `xsd_number_chars/2`.
%   - *`integer`*
%     As `number`, but subsequently transform the value
%     into an integer using the `round/1` function.
%   - *`float`*
%     As `number`, but subsequently transform the value
%     into a float using the `float/1` function.
%   - *`lower`*
%     Translate the value to lower case, preserving
%     the type.
%   - *`upper`*
%     Translate the value to upper case, preserving
%     the type.
%
% In addition, the argument-list can be _conditions_:
%
% - *`Left = Right`*
%   Succeeds if the left-hand unifies with the right-hand.
%   If the left-hand side is a function, this is evaluated.
%   The right-hand side is _never_ evaluated, and thus the
%   condition `content = content` defines that the content
%   of the element is the atom `content`.
%   The functions `lower_case` and `upper_case` can be applied
%   to Right (see example below).
% - *`contains(Haystack, Needle)`*
%   Succeeds if Needle is a sub-list of Haystack.
% - *`XPath`*
%   Succeeds if XPath matches in the currently selected
%   sub-DOM.  For example, the following expression finds
%   an `h3` element inside a `div` element, where the `div`
%   element itself contains an `h2` child with a `strong`
%   child.
%
%   ```
%   //div(h2/strong)/h3
%   ```
%
%   This is equivalent to the conjunction of XPath goals below.
%
%   ```
%   ...,
%   xpath(DOM, //(div), Div),
%   xpath(Div, h2/strong, _),
%   xpath(Div, h3, Result)
%   ```
%
% #### Examples
%
% Match each table-row in DOM:
%
% ```
% xpath(DOM, //tr, TR)
% ```
%
% Match the last cell  of  each   tablerow  in  DOM.  This example
% illustrates that a result can be the input of subsequent `xpath/3`
% queries. Using multiple queries  on   the  intermediate  TR term
% guarantee that all results come from the same table-row:
%
% ```
% xpath(DOM, //tr, TR),
% xpath(TR,  /td(last), TD)
% ```
%
% Match each `href` attribute in an `<a>` element
%
% ```
% xpath(DOM, //a(@href), HREF)
% ```
%
% Suppose we have a table containing  rows where each first column
% is the name of a product with a   link to details and the second
% is the price (a number).  The   following  predicate matches the
% name, URL and price:
%
% ```
% product(DOM, Name, URL, Price) :-
%     xpath(DOM, //tr, TR),
%     xpath(TR, td(1), C1),
%     xpath(C1, /self(normalize_space), Name),
%     xpath(C1, a(@href), URL),
%     xpath(TR, td(2, number), Price).
% ```
%
% Suppose we want to select  books   with  genre="thriller" from a
% tree containing elements `<book genre=...>`
%
% ```
% thriller(DOM, Book) :-
%     xpath(DOM, //book(@genre=thiller), Book).
% ```
%
% Match the elements `<table align="center">` _and_ `<table
% align="CENTER">`:
%
% ```
% //table(@align(lower) = center)
% ```
%
% Get the `width` and `height` of a `div` element as a number,
% and the `div` node itself:
%
% ```
% xpath(DOM, //div(@width(number)=W, @height(number)=H), Div)
% ```
%
% Note that `div` is an infix operator, so parentheses must be
% used in cases like the following:
%
% ```
% xpath(DOM, //(div), Div)
% ```

xpath(DOM, Spec, Content) :-
    in_dom(Spec, DOM, Content).

in_dom(//Spec, DOM, Value) :-
    !,
    element_spec(Spec, Name, Modifiers),
    sub_dom(I, Len, Name, E, DOM),
    modifiers(Modifiers, I, Len, E, Value).
in_dom(/Spec, E, Value) :-
    !,
    element_spec(Spec, Name, Modifiers),
    (   Name == self
    ->  true
    ;   element_name(E, Name)
    ),
    modifiers(Modifiers, 1, 1, E, Value).
in_dom(A/B, DOM, Value) :-
    !,
    in_dom(A, DOM, Value0),
    in_dom(B, Value0, Value).
in_dom(A//B, DOM, Value) :-
    !,
    in_dom(A, DOM, Value0),
    in_dom(//B, Value0, Value).
in_dom(Spec, element(_, _, Content), Value) :-
    element_spec(Spec, Name, Modifiers),
    count_named_elements(Content, Name, CLen),
    CLen > 0,
    nth_element(N, Name, E, Content),
    modifiers(Modifiers, N, CLen, E, Value).

element_spec(Var, _, _) :-
    var(Var),
    !,
    instantiation_error(Var).
element_spec(NS:Term, NS:Name, Modifiers) :-
    !,
    callable_name_arguments(Term, Name0, Modifiers),
    star(Name0, Name).
element_spec(Term, Name, Modifiers) :-
    !,
    callable_name_arguments(Term, Name0, Modifiers),
    star(Name0, Name).

callable_name_arguments(Atom, Name, Arguments) :-
    atom(Atom),
    !,
    Name = Atom, Arguments = [].
callable_name_arguments(Compound, Name, Arguments) :-
    Compound =.. [Name|Arguments].


star(*, _) :- !.
star(Name, Name).


%!  sub_dom(-Index, -Count, +Name, -Sub, +DOM) is nondet.
%
%   Sub is a node in DOM with Name.
%
%   @param Count    is the total number of nodes in the content
%                   list Sub appears that have the same name.
%   @param Index    is the 1-based index of Sub of nodes with
%                   Name.

sub_dom(1, 1, Name, DOM, DOM) :-
    element_name(DOM, Name0),
    \+ Name \= Name0.
sub_dom(N, Len, Name, E, element(_,_,Content)) :-
    !,
    sub_dom_2(N, Len, Name, E, Content).
sub_dom(N, Len, Name, E, Content) :-
    list_si(Content),
    sub_dom_2(N, Len, Name, E, Content).

sub_dom_2(N, Len, Name, Element, Content) :-
    (   count_named_elements(Content, Name, Len),
        nth_element(N, Name, Element, Content)
    ;   member(element(_,_,C2), Content),
        sub_dom_2(N, Len, Name, Element, C2)
    ).


%!  count_named_elements(+Content, +Name, -Count) is det.
%
%   Count is the number of nodes with Name in Content.

count_named_elements(Content, Name, Count) :-
    count_named_elements(Content, Name, 0, Count).

count_named_elements([], _, Count, Count).
count_named_elements([element(Name,_,_)|T], Name0, C0, C) :-
    \+ Name \= Name0,
    !,
    C1 is C0+1,
    count_named_elements(T, Name0, C1, C).
count_named_elements([_|T], Name, C0, C) :-
    count_named_elements(T, Name, C0, C).


%!  nth_element(?N, +Name, -Element, +Content:list) is nondet.
%
%   True if Element is the N-th element with name in Content.

nth_element(N, Name, Element, Content) :-
    nth_element_(1, N, Name, Element, Content).

nth_element_(I, N, Name, E, [H|T]) :-
    element_name(H, Name0),
    \+ Name \= Name0,
    !,
    (   N = I,
        E = H
    ;   I2 is I + 1,
        (   nonvar(N), I2 > N
        ->  !, fail
        ;   true
        ),
        nth_element_(I2, N, Name, E, T)
    ).
nth_element_(I, N, Name, E, [_|T]) :-
    nth_element_(I, N, Name, E, T).


%!  modifiers(+Modifiers, +I, +Clen, +DOM, -Value)
%
%

modifiers([], _, _, Value, Value).
modifiers([H|T], I, L, Value0, Value) :-
    modifier(H, I, L, Value0, Value1),
    modifiers(T, I, L, Value1, Value).

modifier(M, _, _, _, _) :-
    var(M),
    !,
    instantiation_error(M).
modifier(Index, I, L, Value0, Value) :-
    implicit_index_modifier(Index),
    !,
    Value = Value0,
    index_modifier(Index, I, L).
modifier(index(Index), I, L, Value, Value) :-
    !,
    index_modifier(Index, I, L).
modifier(Function, _, _, In, Out) :-
    xpath_function(Function),
    !,
    xpath_function(Function, In, Out).
modifier(Function, _, _, In, Out) :-
    xpath_condition(Function, In),
    Out = In.

implicit_index_modifier(I) :-
    integer(I),
    !.
implicit_index_modifier(last).
implicit_index_modifier(last-_Expr).

index_modifier(Var, I, _L) :-
    var(Var),
    !,
    Var = I.
index_modifier(last, I, L) :-
    !,
    I =:= L.
index_modifier(last-Expr, I, L) :-
    !,
    I =:= L-Expr.
index_modifier(N, I, _) :-
    N =:= I.

xpath_function(self, DOM, DOM).                                % self
xpath_function(content, Element, Value) :-                     % content
    element_content(Element, Value).
xpath_function(text, DOM, Text) :-                             % text
    text_of_dom(DOM, chars, Text).
xpath_function(text(As), DOM, Text) :-                         % text(atom)
    text_of_dom(DOM, As, Text).
xpath_function(normalize_space, DOM, Text) :-                  % normalize_space
    text_of_dom(DOM, chars, Text0),
    normalize_space(Text0, Text).
xpath_function(number, DOM, Number) :-                         % number
    text_of_dom(DOM, chars, Text0),
    normalize_space(Text0, Text),
    catch(xsd_number_chars(Number, Text), _, fail).
xpath_function(@Name, element(_, Attrs, _), Value) :-          % @Name
    (   atom(Name)
    ->  memberchk(Name=Value, Attrs)
    ;   compound(Name)
    ->  Name =.. [AName|AOps],
        memberchk(AName=Value0, Attrs),
        translate_attribute(AOps, Value0, Value)
    ;   member(Name=Value, Attrs)
    ).
xpath_function(quote(Value), _, Value).                         % quote(Value)

xpath_function(self).
xpath_function(content).
xpath_function(text).
xpath_function(text(_)).
xpath_function(normalize_space).
xpath_function(number).
xpath_function(@_).
xpath_function(quote(_)).

translate_attribute([], Value, Value).
translate_attribute([H|T], Value0, Value) :-
    translate_attr(H, Value0, Value1),
    translate_attribute(T, Value1, Value).

translate_attr(number, Value0, Value) :-
    xsd_number_chars(Value, Value0).
translate_attr(integer, Value0, Value) :-
    xsd_number_chars(Value1, Value0),
    Value is round(Value1).
translate_attr(float, Value0, Value) :-
    xsd_number_chars(Value1, Value0),
    Value is float(Value1).
% The implementation of these translations is left for later.
% translate_attr(lower, Value0, Value) :- ...
% translate_attr(upper, Value0, Value) :- ...

xpath_condition(Left = Right, Value) :-                        % =
    !,
    var_or_function(Left, Value, LeftValue),
    process_equality(LeftValue, Right).
xpath_condition(contains(Haystack, Needle), Value) :-          % contains(Haystack, Needle)
    !,
    val_or_function(Haystack, Value, HaystackValue),
    val_or_function(Needle, Value, NeedleValue),
    (   phrase((...,seq(NeedleValue),...), HaystackValue)
    ->  true
    ).
xpath_condition(Spec, Dom) :-
    in_dom(Spec, Dom, _).


%!  process_equality(+Left, +Right) is semidet.
%
%   Provides (very) partial support for XSLT   functions that can be
%   applied according to the XPath 2 specification.
%
%   For example the XPath expression  in   [1],  and  the equivalent
%   Prolog expression in [2], would both   match the HTML element in
%   [3].
%
%     ==
%     [1] //table[align=lower-case(center)]
%     [2] //table(@align=lower_case(center))
%     [3] <table align="CENTER">
%     ==

process_equality(Left, Right) :-
    var(Right),
    !,
    Left = Right.
process_equality(Left, lower_case(Right)) :-
    !,
    downcase_atom(Left, Right).
process_equality(Left, upper_case(Right)) :-
    !,
    upcase_atom(Left, Right).
process_equality(Left, Right) :-
    Left = Right.


var_or_function(Arg, _, Arg) :-
    var(Arg),
    !.
var_or_function(Func, Value0, Value) :-
    xpath_function(Func),
    !,
    xpath_function(Func, Value0, Value).
var_or_function(Value, _, Value).

val_or_function(Arg, _, Arg) :-
    var(Arg),
    !,
    instantiation_error(Arg).
val_or_function(Func, Value0, Value) :-                         % TBD
    xpath_function(Func, Value0, Value),
    !.
val_or_function(Value, _, Value).


%!  text_of_dom(+DOM, +As, -Text:(chars | atom)) is det.
%
%   Text is the joined textual content of DOM.

text_of_dom(DOM, As, Text) :-
    phrase(text_of(DOM), Text0),
    (   As == chars ->
        Text = Text0
    ;   As == atom ->
        atom_chars(Text, Text0)
    ;   domain_error(As, atom_or_chars, xpath)
    ).

text_of(element(_,_,Content)) -->
    text_of_list(Content).
text_of([]) -->
    [].
text_of([H|T]) -->
    text_of(H),
    text_of(T).


text_of_list([]) -->
    [].
text_of_list([H|T]) -->
    text_of_1(H),
    text_of_list(T).


text_of_1(element(_,_,Content)) -->
        text_of_list(Content).
text_of_1([C|Cs]) --> seq([C|Cs]).

% For now, we use number_chars/2 to parse XML numbers.
% If the need arises, we can extend this to additional
% float constants and syntax that may occur in XML files.

xsd_number_chars(Number, Chars) :-
        number_chars(Number, Chars).

normalize_space(Cs0, Cs) :-
        must_be(chars, Cs0),
        no_leading_whitespace(Cs0, Cs1),
        reverse(Cs1, Cs2),
        no_leading_whitespace(Cs2, Cs3),
        reverse(Cs3, Cs4),
        single_intermediate_space(Cs4, Cs).

no_leading_whitespace([], []).
no_leading_whitespace([C0|Cs0], Cs) :-
        (   char_type(C0, whitespace) ->
            no_leading_whitespace(Cs0, Cs)
        ;   Cs = [C0|Cs0]
        ).

single_intermediate_space([], []).
single_intermediate_space([C0|Cs0], [C|Cs]) :-
        (   char_type(C0, whitespace) ->
            no_leading_whitespace(Cs0, Cs1),
            C = ' ',
            single_intermediate_space(Cs1, Cs)
        ;   C = C0,
            single_intermediate_space(Cs0, Cs)
        ).
