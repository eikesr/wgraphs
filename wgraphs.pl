
/*
  TODO: make it a library module.
*/

:- use_module(library(lists), [
        append/3,
        member/2
   ]).

:- use_module(library(ordsets), [
        ord_add_element/3,
        ord_subtract/3,
        ord_union/3,
        ord_union/4
   ]).

%!  vertices(+S_Graph, -Vertices) is det.
%
%   Strips off the  neighbours  lists   of  an  S-representation  to
%   produce  a  list  of  the  vertices  of  the  graph.  (It  is  a
%   characteristic of S-representations that *every* vertex appears,
%   even if it has no  neighbours.).   Vertices  is  in the standard
%   order of terms.
%
%   COPIED FROM ugraphs.pl

vertices([], []) :- !.
vertices([Vertex-_|Graph], [Vertex|Vertices]) :-
    vertices(Graph, Vertices).

%!  vertices_edges_to_wgraph(+Vertices, +Edges, -WGraph) is det.
%
%   Create a WGraph from Vertices and edges.   Given  a graph with a
%   set of Vertices and a set of   Edges,  Graph must unify with the
%   corresponding S-representation. Note that   the vertices without
%   edges will appear in Vertices but not  in Edges. Moreover, it is
%   sufficient for a vertice to appear in Edges.
%
%   ==
%   ?- vertices_edges_to_wgraph([],[1-3,2-4,4-5,1-5], L).
%   L = [1-[3,5], 2-[4], 3-[], 4-[5], 5-[]]
%   ==
%
%   In this case all  vertices  are   defined  implicitly.  The next
%   example shows three unconnected vertices:
%
%   ==
%   ?- vertices_edges_to_wgraph([6,7,8],[1-3,2-4,4-5,1-5], L).
%   L = [1-[3,5], 2-[4], 3-[], 4-[5], 5-[], 6-[], 7-[], 8-[]]
%   ==
%
%   COPIED FROM ugraphs.pl

vertices_edges_to_wgraph(Vertices, Edges, Graph) :-
    sort(Edges, EdgeSet),
    p_to_s_vertices(EdgeSet, IVertexBag),
    append(Vertices, IVertexBag, VertexBag),
    sort(VertexBag, VertexSet),
    p_to_s_group(VertexSet, EdgeSet, Graph).

p_to_s_vertices([], []).
p_to_s_vertices([A-Z-_|Edges], [A,Z|Vertices]) :-
    p_to_s_vertices(Edges, Vertices).


p_to_s_group([], _, []).
p_to_s_group([Vertex|Vertices], EdgeSet, [Vertex-Neibs|G]) :-
    p_to_s_group(EdgeSet, Vertex, Neibs, RestEdges),
    p_to_s_group(Vertices, RestEdges, G).


p_to_s_group([V1-X-W|Edges], V2, [X-W|Neibs], RestEdges) :- V1 == V2,
    !,
    p_to_s_group(Edges, V2, Neibs, RestEdges).
p_to_s_group(Edges, _, [], Edges).

%!  Add vertices
%
%   COPIED FROM ugraphs.pl

add_vertices(Graph, Vertices, NewGraph) :-
    msort(Vertices, V1),
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


%!  del_vertices(+Graph, +Vertices, -NewGraph) is det.
%
%   Unify NewGraph with a new graph obtained by deleting the list of
%   Vertices and all the edges that start from  or go to a vertex in
%   Vertices to the Graph. Example:
%
%   ==
%   ?- del_vertices([1-[3,5],2-[4],3-[],4-[5],5-[],6-[],7-[2,6],8-[]],
%                   [2,1],
%                   NL).
%   NL = [3-[],4-[5],5-[],6-[],7-[6],8-[]]
%   ==
%
%   @compat Upto 5.6.48 the argument order was (+Vertices, +Graph,
%   -NewGraph). Both YAP and SWI-Prolog have changed the argument
%   order for compatibility with recent SICStus as well as
%   consistency with del_edges/3.

del_vertices(Graph, Vertices, NewGraph) :-
    sort(Vertices, V1),
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

%% oset_diff(+InOSet, +NotInOSet, -Diff)
%   ordered set difference

oset_diff([], _Not, []).
oset_diff([H1|T1], L2, Diff) :-
    diff21(L2, H1, T1, Diff).

diff21([], H1, T1, [H1|T1]).
diff21([H2|T2], H1, T1, Diff) :-
    compare(Order, H1, H2),
    diff3(Order, H1, T1, H2, T2, Diff).

diff12([], _H2, _T2, []).
diff12([H1|T1], H2, T2, Diff) :-
    compare(Order, H1, H2),
    diff3(Order, H1, T1, H2, T2, Diff).

diff3(<,  H1, T1,  H2, T2, [H1|Diff]) :-
    diff12(T1, H2, T2, Diff).
diff3(=, _H1, T1, _H2, T2, Diff) :-
    oset_diff(T1, T2, Diff).
diff3(>,  H1, T1, _H2, T2, Diff) :-
diff21(T2, H1, T1, Diff).

