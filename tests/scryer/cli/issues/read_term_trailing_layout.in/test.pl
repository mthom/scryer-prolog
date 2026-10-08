:- use_module(library(charsio)).
:- use_module(library(format)).
:- use_module(library(lists)).

read_to_eof(S, R) :-
    read_term(S, T, []),
    (   T == end_of_file -> R = T
    ;   read_to_eof(S, R)
    ).

% Reads every term of File and prints how the read after the last term ends.
read_file(File) :-
    open(File, read, S),
    catch(read_to_eof(S, R), error(E, C), R = error(E, C)),
    close(S),
    format("~a: ~q~n", [File, R]).

read_chars(Name-Cs) :-
    catch(read_term_from_chars(Cs, T, []), error(E, _), T = E),
    format("~a: ~q~n", [Name, T]).

layout_at_eof :-
    maplist(read_file, ['term_only.pl', 'blank_line.pl', 'trailing_space.pl',
                        'comment_line.pl', 'comment_no_newline.pl',
                        'block_comment.pl', 'only_newline.pl',
                        'only_comment.pl', 'empty.pl']).

incomplete_at_eof :-
    maplist(read_file, ['unterminated_block_comment.pl', 'partial_term.pl',
                        'lone_slash.pl', 'unterminated_quote.pl']).

chars_at_eof :-
    maplist(read_chars, [space-" ", newline-"\n", comment-"% c", empty-"",
                         atom-"a", unterminated_quote-"'abc", lone_slash-"/",
                         term-"a. ", layout_before_paren-" (a,b). ",
                         comment_before_term-"% c\na. "]).

error_lines :-
    maplist(read_file, ['error_first_term.pl', 'error_after_layout.pl',
                        'error_after_block_comment.pl']).
