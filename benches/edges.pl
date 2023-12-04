:- use_module(library(clpb)).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Contiguous United States and DC as they appear in SGB:
    http://www-cs-faculty.stanford.edu/~uno/sgb.html
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

edge(al, fl).
edge(al, ga).
edge(al, ms).
edge(al, tn).
edge(ar, la).
edge(ar, mo).
edge(ar, ms).
edge(ar, ok).
edge(ar, tn).
edge(ar, tx).
edge(az, ca).
edge(az, nm).
edge(az, nv).
edge(az, ut).
edge(ca, nv).
edge(ca, or).
edge(co, ks).
edge(co, ne).
edge(co, nm).
edge(co, ok).
edge(co, ut).
edge(co, wy).
edge(ct, ma).
edge(ct, ny).
edge(ct, ri).
edge(dc, md).
edge(dc, va).
edge(de, md).
edge(de, nj).
edge(de, pa).
edge(fl, ga).
edge(ga, nc).
edge(ga, sc).
edge(ga, tn).
edge(ia, il).
edge(ia, mn).
edge(ia, mo).
edge(ia, ne).
edge(ia, sd).
edge(ia, wi).
edge(id, mt).
edge(id, nv).
edge(id, or).
edge(id, ut).
edge(id, wa).
edge(id, wy).
edge(il, in).
edge(il, ky).
edge(il, mo).
edge(il, wi).
edge(in, ky).
edge(in, mi).
edge(in, oh).
edge(ks, mo).
edge(ks, ne).
edge(ks, ok).
edge(ky, mo).
edge(ky, oh).
edge(ky, tn).
edge(ky, va).
edge(ky, wv).
edge(la, ms).
edge(la, tx).
edge(ma, nh).
edge(ma, ny).
edge(ma, ri).
edge(ma, vt).
edge(md, pa).
edge(md, va).
edge(md, wv).
edge(me, nh).
edge(mi, oh).
edge(mi, wi).
edge(mn, nd).
edge(mn, sd).
edge(mn, wi).
edge(mo, ne).
edge(mo, ok).
edge(mo, tn).
edge(ms, tn).
edge(mt, nd).
edge(mt, sd).
edge(mt, wy).
edge(nc, sc).
edge(nc, tn).
edge(nc, va).
edge(nd, sd).
edge(ne, sd).
edge(ne, wy).
edge(nh, vt).
edge(nj, ny).
edge(nj, pa).
edge(nm, ok).
edge(nm, tx).
edge(nv, or).
edge(nv, ut).
edge(ny, pa).
edge(ny, vt).
edge(oh, pa).
edge(oh, wv).
edge(ok, tx).
edge(or, wa).
edge(pa, wv).
edge(sd, wy).
edge(tn, va).
edge(ut, wy).
edge(va, wv).

independent_set(G, *(NBs)) :-
        findall(U-V, (edge(U, V),G@<U), Edges),
        setof(U, V^(member(U-V, Edges);member(V-U, Edges)), Nodes),
        pairs_keys_values(Pairs, Nodes, _),
        list_to_assoc(Pairs, Assoc),
        maplist(not_both(Assoc), Edges, NBs).

not_both(Assoc, U-V, ~BU + ~BV) :-
        get_assoc(U, Assoc, BU),
        get_assoc(V, Assoc, BV).

independent_set_count(G, Count) :- independent_set(G, Sat), sat_count(Sat, Count).
