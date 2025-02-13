% NOTE: the tests in this file will need to be changed once
% `open(stream(S1), read, _, NewOptions)` creates a new stream handle `S2` instead of updating
% the options in `S1`. In that case, that specific query will need to be updated
% to instead change the options of `S1`.

alias_dropped_stream :-
    open("README.md", read, S, [alias(readme)]),
    open(stream(S), read, _, [alias(not_readme)]),
    close(S),
    stream_property(readme, file_name(_)). % Should throw an existence_error

realias_user_output :-
    current_output(S),
    open(stream(S), read, _, [alias(not_user_output)]),
    stream_property(S, alias(user_output)). % Should succeed

set_output_alias :-
    set_output(user_error),
    write(user_output, hello). % Should write into stderr, not stdout
