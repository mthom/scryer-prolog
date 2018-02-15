pub static CONTROL: &str = ":- op(700, xfx, \\=).

                            once(G) :- G, !.

                            \\=(X, X) :- !, false.
                            \\=(_, _).

                            between(Lower, Upper, Lower) :-
                               Lower =< Upper.
                            between(Lower1, Upper, X) :-
                               Lower1 < Upper,
                               Lower2 is Lower1 + 1,
                               between(Lower2, Upper, X).";
