:- module(b, [
    make_goal_b_raw/1,
    make_goal_b_scoped/1,
    make_goal_b_scoped_alt/1
]).

:- use_module(library(lambda)).

% Private to module b
q.

make_goal_b_raw(\q).

% Giving the call to private q/0 an explicit module
make_goal_b_scoped(\(b:q)).

% Giving the entire labda a scope
make_goal_b_scoped_alt(b:(\q)).
