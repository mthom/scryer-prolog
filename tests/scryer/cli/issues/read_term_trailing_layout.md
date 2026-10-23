If only layout text (whitespace, comments) is left before the end of the stream,
`read_term/2,3` and `read_term_from_chars/3` must return `end_of_file`, not a
syntax error.

```trycmd
$ scryer-prolog -f --no-add-history test.pl -g layout_at_eof -g halt
term_only.pl: end_of_file
blank_line.pl: end_of_file
trailing_space.pl: end_of_file
comment_line.pl: end_of_file
comment_no_newline.pl: end_of_file
block_comment.pl: end_of_file
only_newline.pl: end_of_file
only_comment.pl: end_of_file
empty.pl: end_of_file

```

End of stream after any other character is still a syntax error (see #1887).

```trycmd
$ scryer-prolog -f --no-add-history test.pl -g incomplete_at_eof -g halt
unterminated_block_comment.pl: error(syntax_error(incomplete_reduction),read_term/3:1)
partial_term.pl: error(syntax_error(incomplete_reduction),read_term/3:1)
lone_slash.pl: error(syntax_error(incomplete_reduction),read_term/3:1)
unterminated_quote.pl: error(syntax_error(incomplete_reduction),read_term/3:0)

```

```trycmd
$ scryer-prolog -f --no-add-history test.pl -g chars_at_eof -g halt
space: end_of_file
newline: end_of_file
comment: end_of_file
empty: end_of_file
atom: syntax_error(incomplete_reduction)
unterminated_quote: syntax_error(incomplete_reduction)
lone_slash: syntax_error(incomplete_reduction)
term: a
layout_before_paren: a,b
comment_before_term: a

```

Layout before a term still counts towards the line number of a syntax error.

```trycmd
$ scryer-prolog -f --no-add-history test.pl -g error_lines -g halt
error_first_term.pl: error(syntax_error(incomplete_reduction),read_term/3:4)
error_after_layout.pl: error(syntax_error(incomplete_reduction),read_term/3:5)
error_after_block_comment.pl: error(syntax_error(incomplete_reduction),read_term/3:7)

```

```trycmd
$ scryer-prolog -f --no-add-history consult_error.pl -g halt
   error(syntax_error(incomplete_reduction),read_term/3:4).

```
