/*  Author:        R.A.O'Keefe, Vitor Santos Costa, Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  1984-2021, VU University Amsterdam
                              CWI, Amsterdam
                              SWI-Prolog Solutions .b.v
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
*/

:- module(ugraphs,
          [ add_edges/3,                % +Graph, +Edges, -NewGraph
            add_vertices/3,             % +Graph, +Vertices, -NewGraph
            complement/2,               % +Graph, -NewGraph
            compose/3,                  % +LeftGraph, +RightGraph, -NewGraph
            del_edges/3,                % +Graph, +Edges, -NewGraph
            del_vertices/3,             % +Graph, +Vertices, -NewGraph
            edges/2,                    % +Graph, -Edges
            neighbors/3,                % +Vertex, +Graph, -Vertices
            neighbours/3,               % +Vertex, +Graph, -Vertices
            reachable/3,                % +Vertex, +Graph, -Vertices
            top_sort/2,                 % +Graph, -Sort
            top_sort/3,                 % +Graph, -Sort0, -Sort
            transitive_closure/2,       % +Graph, -Closure
            transpose_ugraph/2,         % +Graph, -NewGraph
            vertices/2,                 % +Graph, -Vertices
            vertices_edges_to_ugraph/3, % +Vertices, +Edges, -Graph
            ugraph_union/3,             % +Graph1, +Graph2, -Graph
            connect_ugraph/3            % +Graph1, -Start, -Graph
          ]).

/** Graph manipulation library

The S-representation of a graph is  a list of (vertex-neighbours) pairs,
where the pairs are in standard order   (as produced by keysort) and the
neighbours of each vertex are also  in   standard  order (as produced by
sort). This form is convenient for many calculations.

A   new   UGraph   from    raw    data     can    be    created    using
`vertices_edges_to_ugraph/3`.

Adapted to support some of  the   functionality  of  the SICStus ugraphs
library by Vitor Santos Costa.

Ported from YAP 5.0.1 to SWI-Prolog by Jan Wielemaker.

Ported from SWI-Prolog to Scryer by [Adrián Arroyo Calle](https://adrianistan.eu)

License: BSD-2 or Artistic 2.0
*/

:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(ordsets)).

%% vertices(+Graph, -Vertices)
%
% Unify Vertices with all vertices appearing in Graph. Example:
%
% ```
% ?- vertices([1-[3,5],2-[4],3-[],4-[5],5-[]], L).
%    L = [1, 2, 3, 4, 5]
% ```

vertices([], []) :- !.
vertices([Vertex-_|Graph], [Vertex|Vertices]) :-
    vertices(Graph, Vertices).


%% vertices_edges_to_ugraph(+Vertices, +Edges, -UGraph) is det.
%
% Create a UGraph from Vertices and edges.   Given  a graph with a
% set of Vertices and a set of   Edges,  Graph must unify with the
% corresponding S-representation. Note that   the vertices without
% edges will appear in Vertices but not  in Edges. Moreover, it is
% sufficient for a vertice to appear in Edges.
%
% ```
% ?- vertices_edges_to_ugraph([],[1-3,2-4,4-5,1-5], L).
%    L = [1-[3,5], 2-[4], 3-[], 4-[5], 5-[]]
% ```
% 
% In this case all  vertices  are   defined  implicitly.  The next
% example shows three unconnected vertices:
%
% ```
% ?- vertices_edges_to_ugraph([6,7,8],[1-3,2-4,4-5,1-5], L).
%    L = [1-[3,5], 2-[4], 3-[], 4-[5], 5-[], 6-[], 7-[], 8-[]]
% ```

vertices_edges_to_ugraph(Vertices, Edges, Graph) :-
    sort(Edges, EdgeSet),
    p_to_s_vertices(EdgeSet, IVertexBag),
    append(Vertices, IVertexBag, VertexBag),
    sort(VertexBag, VertexSet),
    p_to_s_group(VertexSet, EdgeSet, Graph).


%% add_vertices(+Graph, +Vertices, -NewGraph)
%
% Unify NewGraph with a new  graph  obtained   by  adding  the list of
% Vertices to Graph. Example:
%
% ```
% ?- add_vertices([1-[3,5],2-[]], [0,1,2,9], NG).
%    NG = [0-[], 1-[3,5], 2-[], 9-[]]
% ```

% replace with real msort/2 when available
msort_(List, Sorted) :-
    pairs_keys(Pairs, List),
    keysort(Pairs, SortedPairs),
    pairs_keys(SortedPairs, Sorted).

add_vertices(Graph, Vertices, NewGraph) :-
    % msort/2 not available in Scryer Prolog yet: msort(Vertices, V1),
    msort_(Vertices, V1),
    add_vertices_to_s_graph(V1, Graph, NewGraph).

add_vertices_to_s_graph(L, [], NL) :-
    !,
    add_empty_vertices(L, NL).
add_vertices_to_s_graph([], L, L) :- !.
add_vertices_to_s_graph([V1|VL], [V-Edges|G], NGL) :-
    compare(Res, V1, V),
    add_vertices_to_s_graph(Res, V1, VL, V, Edges, G, NGL).

add_vertices_to_s_graph(=, _, VL, V, Edges, G, [V-Edges|NGL]) :-
    add_vertices_to_s_graph(VL, G, NGL).
add_vertices_to_s_graph(<, V1, VL, V, Edges, G, [V1-[]|NGL]) :-
    add_vertices_to_s_graph(VL, [V-Edges|G], NGL).
add_vertices_to_s_graph(>, V1, VL, V, Edges, G, [V-Edges|NGL]) :-
    add_vertices_to_s_graph([V1|VL], G, NGL).

add_empty_vertices([], []).
add_empty_vertices([V|G], [V-[]|NG]) :-
    add_empty_vertices(G, NG).

%% del_vertices(+Graph, +Vertices, -NewGraph) is det.
%
% Unify NewGraph with a new graph obtained by deleting the list of
% Vertices and all the edges that start from  or go to a vertex in
% Vertices to the Graph. Example:
%
% ```
% ?- del_vertices([1-[3,5],2-[4],3-[],4-[5],5-[],6-[],7-[2,6],8-[]],
%               [2,1],
%               NL).
%    NL = [3-[],4-[5],5-[],6-[],7-[6],8-[]]
% ```

del_vertices(Graph, Vertices, NewGraph) :-
    sort(Vertices, V1),             % JW: was msort
    (   V1 = []
    ->  Graph = NewGraph
    ;   del_vertices(Graph, V1, V1, NewGraph)
    ).

del_vertices(G, [], V1, NG) :-
    !,
    del_remaining_edges_for_vertices(G, V1, NG).
del_vertices([], _, _, []).
del_vertices([V-Edges|G], [V0|Vs], V1, NG) :-
    compare(Res, V, V0),
    split_on_del_vertices(Res, V,Edges, [V0|Vs], NVs, V1, NG, NGr),
    del_vertices(G, NVs, V1, NGr).

del_remaining_edges_for_vertices([], _, []).
del_remaining_edges_for_vertices([V0-Edges|G], V1, [V0-NEdges|NG]) :-
    ord_subtract(Edges, V1, NEdges),
    del_remaining_edges_for_vertices(G, V1, NG).

split_on_del_vertices(<, V, Edges, Vs, Vs, V1, [V-NEdges|NG], NG) :-
    ord_subtract(Edges, V1, NEdges).
split_on_del_vertices(>, V, Edges, [_|Vs], Vs, V1, [V-NEdges|NG], NG) :-
    ord_subtract(Edges, V1, NEdges).
split_on_del_vertices(=, _, _, [_|Vs], Vs, _, NG, NG).

%% add_edges(+Graph, +Edges, -NewGraph)
%
% Unify NewGraph with a new graph obtained by adding the list of Edges
% to Graph. Example:
%
% ```
% ?- add_edges([1-[3,5],2-[4],3-[],4-[5],
%             5-[],6-[],7-[],8-[]],
%            [1-6,2-3,3-2,5-7,3-2,4-5],
%            NL).
%    NL = [1-[3,5,6], 2-[3,4], 3-[2], 4-[5],
%     5-[7], 6-[], 7-[], 8-[]]
% ```

add_edges(Graph, Edges, NewGraph) :-
    p_to_s_graph(Edges, G1),
    ugraph_union(Graph, G1, NewGraph).

%% ugraph_union(+Graph1, +Graph2, -NewGraph)
%
% NewGraph is the union of Graph1 and Graph2. Example:
%
% ```
% ?- ugraph_union([1-[2],2-[3]],[2-[4],3-[1,2,4]],L).
%    L = [1-[2], 2-[3,4], 3-[1,2,4]]
% ```

ugraph_union(Set1, [], Set1) :- !.
ugraph_union([], Set2, Set2) :- !.
ugraph_union([Head1-E1|Tail1], [Head2-E2|Tail2], Union) :-
    compare(Order, Head1, Head2),
    ugraph_union(Order, Head1-E1, Tail1, Head2-E2, Tail2, Union).

ugraph_union(=, Head-E1, Tail1, _-E2, Tail2, [Head-Es|Union]) :-
    ord_union(E1, E2, Es),
    ugraph_union(Tail1, Tail2, Union).
ugraph_union(<, Head1, Tail1, Head2, Tail2, [Head1|Union]) :-
    ugraph_union(Tail1, [Head2|Tail2], Union).
ugraph_union(>, Head1, Tail1, Head2, Tail2, [Head2|Union]) :-
    ugraph_union([Head1|Tail1], Tail2, Union).

%% del_edges(+Graph, +Edges, -NewGraph)
%
% Unify NewGraph with a new graph  obtained   by  removing the list of
% Edges from Graph. Notice that no vertices are deleted. Example:
%
% ```
% ?- del_edges([1-[3,5],2-[4],3-[],4-[5],5-[],6-[],7-[],8-[]],
%            [1-6,2-3,3-2,5-7,3-2,4-5,1-3],
%            NL).
%    NL = [1-[5],2-[4],3-[],4-[],5-[],6-[],7-[],8-[]]
% ```

del_edges(Graph, Edges, NewGraph) :-
    p_to_s_graph(Edges, G1),
    graph_subtract(Graph, G1, NewGraph).

%% graph_subtract(+Set1, +Set2, ?Difference)
%
% Is based on `ord_subtract/3`

graph_subtract(Set1, [], Set1) :- !.
graph_subtract([], _, []).
graph_subtract([Head1-E1|Tail1], [Head2-E2|Tail2], Difference) :-
    compare(Order, Head1, Head2),
    graph_subtract(Order, Head1-E1, Tail1, Head2-E2, Tail2, Difference).

graph_subtract(=, H-E1,     Tail1, _-E2,     Tail2, [H-E|Difference]) :-
    ord_subtract(E1,E2,E),
    graph_subtract(Tail1, Tail2, Difference).
graph_subtract(<, Head1, Tail1, Head2, Tail2, [Head1|Difference]) :-
    graph_subtract(Tail1, [Head2|Tail2], Difference).
graph_subtract(>, Head1, Tail1, _,     Tail2, Difference) :-
    graph_subtract([Head1|Tail1], Tail2, Difference).

%% edges(+Graph, -Edges)
%
% Unify Edges with all edges appearing in Graph. Example:
%
% ```
% ?- edges([1-[3,5],2-[4],3-[],4-[5],5-[]], L).
%    L = [1-3, 1-5, 2-4, 4-5]
% ```

edges(Graph, Edges) :-
    s_to_p_graph(Graph, Edges).

p_to_s_graph(P_Graph, S_Graph) :-
    sort(P_Graph, EdgeSet),
    p_to_s_vertices(EdgeSet, VertexBag),
    sort(VertexBag, VertexSet),
    p_to_s_group(VertexSet, EdgeSet, S_Graph).


p_to_s_vertices([], []).
p_to_s_vertices([A-Z|Edges], [A,Z|Vertices]) :-
    p_to_s_vertices(Edges, Vertices).


p_to_s_group([], _, []).
p_to_s_group([Vertex|Vertices], EdgeSet, [Vertex-Neibs|G]) :-
    p_to_s_group(EdgeSet, Vertex, Neibs, RestEdges),
    p_to_s_group(Vertices, RestEdges, G).


p_to_s_group([V1-X|Edges], V2, [X|Neibs], RestEdges) :- V1 == V2,
    !,
    p_to_s_group(Edges, V2, Neibs, RestEdges).
p_to_s_group(Edges, _, [], Edges).



s_to_p_graph([], []) :- !.
s_to_p_graph([Vertex-Neibs|G], P_Graph) :-
    s_to_p_graph(Neibs, Vertex, P_Graph, Rest_P_Graph),
    s_to_p_graph(G, Rest_P_Graph).


s_to_p_graph([], _, P_Graph, P_Graph) :- !.
s_to_p_graph([Neib|Neibs], Vertex, [Vertex-Neib|P], Rest_P) :-
    s_to_p_graph(Neibs, Vertex, P, Rest_P).

%% transitive_closure(+Graph, -Closure)
%
% Generate the graph Closure  as  the   transitive  closure  of Graph.
% Example:
%
% ```
% ?- transitive_closure([1-[2,3],2-[4,5],4-[6]],L).
%    L = [1-[2,3,4,5,6], 2-[4,5,6], 4-[6]]
% ```

transitive_closure(Graph, Closure) :-
    warshall(Graph, Graph, Closure).

warshall([], Closure, Closure) :- !.
warshall([V-_|G], E, Closure) :-
    memberchk(V-Y, E),      %  Y := E(v)
    warshall(E, V, Y, NewE),
    warshall(G, NewE, Closure).


warshall([X-Neibs|G], V, Y, [X-NewNeibs|NewG]) :-
    memberchk(V, Neibs),
    !,
    ord_union(Neibs, Y, NewNeibs),
    warshall(G, V, Y, NewG).
warshall([X-Neibs|G], V, Y, [X-Neibs|NewG]) :-
    !,
    warshall(G, V, Y, NewG).
warshall([], _, _, []).

%% transpose_ugraph(Graph, NewGraph) is det.
%
% Unify NewGraph with a new graph obtained from Graph by replacing
% all edges of the form V1-V2 by edges of the form V2-V1. The cost
% is O(|V|\*log(|V|)). Notice that an undirected   graph is its own
% transpose. Example:
%
% ```
% ?- transpose([1-[3,5],2-[4],3-[],4-[5],
%               5-[],6-[],7-[],8-[]], NL).
%    NL = [1-[],2-[],3-[1],4-[2],5-[1,4],6-[],7-[],8-[]]
% ```

transpose_ugraph(Graph, NewGraph) :-
    edges(Graph, Edges),
    vertices(Graph, Vertices),
    flip_edges(Edges, TransposedEdges),
    vertices_edges_to_ugraph(Vertices, TransposedEdges, NewGraph).

flip_edges([], []).
flip_edges([Key-Val|Pairs], [Val-Key|Flipped]) :-
    flip_edges(Pairs, Flipped).

%% compose(+LeftGraph, +RightGraph, -NewGraph)
%
% Compose NewGraph by connecting the  _drains_   of  LeftGraph  to the
% _sources_ of RightGraph. Example:
%
% ```
% ?- compose([1-[2],2-[3]],[2-[4],3-[1,2,4]],L).
%    L = [1-[4], 2-[1,2,4], 3-[]]
% ```

compose(G1, G2, Composition) :-
    vertices(G1, V1),
    vertices(G2, V2),
    ord_union(V1, V2, V),
    compose(V, G1, G2, Composition).

compose([], _, _, []) :- !.
compose([Vertex|Vertices], [Vertex-Neibs|G1], G2,
        [Vertex-Comp|Composition]) :-
    !,
    compose1(Neibs, G2, [], Comp),
    compose(Vertices, G1, G2, Composition).
compose([Vertex|Vertices], G1, G2, [Vertex-[]|Composition]) :-
    compose(Vertices, G1, G2, Composition).


compose1([V1|Vs1], [V2-N2|G2], SoFar, Comp) :-
    compare(Rel, V1, V2),
    !,
    compose1(Rel, V1, Vs1, V2, N2, G2, SoFar, Comp).
compose1(_, _, Comp, Comp).


compose1(<, _, Vs1, V2, N2, G2, SoFar, Comp) :-
    !,
    compose1(Vs1, [V2-N2|G2], SoFar, Comp).
compose1(>, V1, Vs1, _, _, G2, SoFar, Comp) :-
    !,
    compose1([V1|Vs1], G2, SoFar, Comp).
compose1(=, V1, Vs1, V1, N2, G2, SoFar, Comp) :-
    ord_union(N2, SoFar, Next),
    compose1(Vs1, G2, Next, Comp).

%% top_sort(+Graph, -Sorted) is semidet.
%
% Sorted is a  topological  sorted  list   of  nodes  in  Graph. A
% toplogical sort is possible  if  the   graph  is  connected  and
% acyclic. In the example we show   how  topological sorting works
% for a linear graph:
%
% ```
% ?- top_sort([1-[2], 2-[3], 3-[]], L).
%    L = [1, 2, 3]
% ```

top_sort(Graph, Sorted) :-
    vertices_and_zeros(Graph, Vertices, Counts0),
    count_edges(Graph, Vertices, Counts0, Counts1),
    select_zeros(Counts1, Vertices, Zeros),
    top_sort(Zeros, Sorted, Graph, Vertices, Counts1).

%% top_sort(+Graph, -Sorted, ?Tail) is semidet.
%
% The  predicate  `top_sort/3`  is  a  difference  list  version  of
% `top_sort/2`.

top_sort(Graph, Sorted0, Sorted) :-
    vertices_and_zeros(Graph, Vertices, Counts0),
    count_edges(Graph, Vertices, Counts0, Counts1),
    select_zeros(Counts1, Vertices, Zeros),
    top_sort(Zeros, Sorted, Sorted0, Graph, Vertices, Counts1).


vertices_and_zeros([], [], []) :- !.
vertices_and_zeros([Vertex-_|Graph], [Vertex|Vertices], [0|Zeros]) :-
    vertices_and_zeros(Graph, Vertices, Zeros).


count_edges([], _, Counts, Counts) :- !.
count_edges([_-Neibs|Graph], Vertices, Counts0, Counts2) :-
    incr_list(Neibs, Vertices, Counts0, Counts1),
    count_edges(Graph, Vertices, Counts1, Counts2).


incr_list([], _, Counts, Counts) :- !.
incr_list([V1|Neibs], [V2|Vertices], [M|Counts0], [N|Counts1]) :-
    V1 == V2,
    !,
    N is M+1,
    incr_list(Neibs, Vertices, Counts0, Counts1).
incr_list(Neibs, [_|Vertices], [N|Counts0], [N|Counts1]) :-
    incr_list(Neibs, Vertices, Counts0, Counts1).


select_zeros([], [], []) :- !.
select_zeros([0|Counts], [Vertex|Vertices], [Vertex|Zeros]) :-
    !,
    select_zeros(Counts, Vertices, Zeros).
select_zeros([_|Counts], [_|Vertices], Zeros) :-
    select_zeros(Counts, Vertices, Zeros).



top_sort([], [], Graph, _, Counts) :-
    !,
    vertices_and_zeros(Graph, _, Counts).
top_sort([Zero|Zeros], [Zero|Sorted], Graph, Vertices, Counts1) :-
    graph_memberchk(Zero-Neibs, Graph),
    decr_list(Neibs, Vertices, Counts1, Counts2, Zeros, NewZeros),
    top_sort(NewZeros, Sorted, Graph, Vertices, Counts2).

top_sort([], Sorted0, Sorted0, Graph, _, Counts) :-
    !,
    vertices_and_zeros(Graph, _, Counts).
top_sort([Zero|Zeros], [Zero|Sorted], Sorted0, Graph, Vertices, Counts1) :-
    graph_memberchk(Zero-Neibs, Graph),
    decr_list(Neibs, Vertices, Counts1, Counts2, Zeros, NewZeros),
    top_sort(NewZeros, Sorted, Sorted0, Graph, Vertices, Counts2).

graph_memberchk(Element1-Edges, [Element2-Edges2|_]) :-
    Element1 == Element2,
    !,
    Edges = Edges2.
graph_memberchk(Element, [_|Rest]) :-
    graph_memberchk(Element, Rest).


decr_list([], _, Counts, Counts, Zeros, Zeros) :- !.
decr_list([V1|Neibs], [V2|Vertices], [1|Counts1], [0|Counts2], Zi, Zo) :-
    V1 == V2,
    !,
    decr_list(Neibs, Vertices, Counts1, Counts2, [V2|Zi], Zo).
decr_list([V1|Neibs], [V2|Vertices], [N|Counts1], [M|Counts2], Zi, Zo) :-
    V1 == V2,
    !,
    M is N-1,
    decr_list(Neibs, Vertices, Counts1, Counts2, Zi, Zo).
decr_list(Neibs, [_|Vertices], [N|Counts1], [N|Counts2], Zi, Zo) :-
    decr_list(Neibs, Vertices, Counts1, Counts2, Zi, Zo).



%% neighbours(+Vertex, +Graph, -Neigbours) is det.
%
% Neigbours is a sorted list of  the   neighbours  of Vertex in Graph.
% Example:
%
% ```
% ?- neighbours(4,[1-[3,5],2-[4],3-[],
%                4-[1,2,7,5],5-[],6-[],7-[],8-[]], NL).
%    NL = [1,2,7,5]
% ```

%% neighbors(+Vertex, +Graph, -Neigbours) is det.
%
% Same as `neighbours/3`.

neighbors(Vertex, Graph, Neig) :-
    neighbours(Vertex, Graph, Neig).

neighbours(V,[V0-Neig|_],Neig) :-
    V == V0,
    !.
neighbours(V,[_|G],Neig) :-
    neighbours(V,G,Neig).


%% connect_ugraph(+UGraphIn, -Start, -UGraphOut) is det.
%
% Adds Start as an additional vertex that is connected to all vertices
% in UGraphIn. This can be used to   create  an topological sort for a
% not connected graph. Start is before any   vertex in UGraphIn in the
% standard order of terms.  No vertex in UGraphIn can be a variable.
%
% Can be used to order a not-connected graph as follows:
%
% ```
% top_sort_unconnected(Graph, Vertices) :-
%   (   top_sort(Graph, Vertices)
%   ->  true
%   ;   connect_ugraph(Graph, Start, Connected),
%       top_sort(Connected, Ordered0),
%       Ordered0 = [Start|Vertices]
%   ).
% ```

connect_ugraph([], 0, []) :- !.
connect_ugraph(Graph, Start, [Start-Vertices|Graph]) :-
    vertices(Graph, Vertices),
    Vertices = [First|_],
    before(First, Start).

%% before(+Term, -Before) is det.
%
% Unify Before to a term that comes   before  Term in the standard
% order of terms.
%
% Throws `instantiation_error` if Term is unbound.

before(X, _) :-
    var(X),
    !,
    instantiation_error(X).
before(Number, Start) :-
    number(Number),
    !,
    Start is Number - 1.
before(_, 0).


%% complement(+UGraphIn, -UGraphOut)
%
% UGraphOut is a ugraph with an  edge   between  all vertices that are
% _not_ connected in UGraphIn and  all   edges  from UGraphIn removed.
% Example:
%
% ```
% ?- complement([1-[3,5],2-[4],3-[],
%              4-[1,2,7,5],5-[],6-[],7-[],8-[]], NL).
%    NL = [1-[2,4,6,7,8],2-[1,3,5,6,7,8],3-[1,2,4,5,6,7,8],
%     4-[3,5,6,8],5-[1,2,3,4,6,7,8],6-[1,2,3,4,5,7,8],
%     7-[1,2,3,4,5,6,8],8-[1,2,3,4,5,6,7]]
% ```


% TODO: Simple two-step algorithm. You could be smarter, I suppose.

complement(G, NG) :-
    vertices(G,Vs),
    complement(G,Vs,NG).

complement([], _, []).
complement([V-Ns|G], Vs, [V-INs|NG]) :-
    ord_add_element(Ns,V,Ns1),
    ord_subtract(Vs,Ns1,INs),
    complement(G, Vs, NG).

%% reachable(+Vertex, +UGraph, -Vertices)
%
% True when Vertices is  an  ordered   set  of  vertices  reachable in
% UGraph, including Vertex.  Example:
%
% ```
% ?- reachable(1,[1-[3,5],2-[4],3-[],4-[5],5-[]],V).
%    V = [1, 3, 5]
% ```

reachable(N, G, Rs) :-
    reachable([N], G, [N], Rs).

reachable([], _, Rs, Rs).
reachable([N|Ns], G, Rs0, RsF) :-
    neighbours(N, G, Nei),
    ord_union(Rs0, Nei, Rs1, D),
    append(Ns, D, Nsi),
    reachable(Nsi, G, Rs1, RsF).
