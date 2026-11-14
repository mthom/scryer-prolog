% read/1 must return end_of_file when only layout text (whitespace, complete comments)
% follows the last clause, and must still raise a syntax error for an incomplete token or term.
t(F) :-
    open(F, read, S),
    catch((read(S, X), read(S, Y)), error(E, _), (X = none, Y = error(E))),
    close(S),
    write(F: X/Y), nl.
test :- maplist(t, ['spaces.txt', 'line_comment.txt', 'block_comment.txt', 'only_layout.txt',
                    'open_quote.txt', 'open_comment.txt', 'no_end.txt']).
