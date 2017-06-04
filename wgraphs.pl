
:- module(wgraphs,
          [ add_edges/3,                % +Graph, +Edges, -NewGraph
            add_vertices/3,             % +Graph, +Vertices, -NewGraph
%           compose/3,                  % +LeftGraph, +RightGraph, -NewGraph
            del_edges/3,                % +Graph, +Edges, -NewGraph
            del_vertices/3,             % +Graph, +Vertices, -NewGraph
            edges/2,                    % +Graph, -Edges
            neighbors/3,                % +Vertex, +Graph, -Vertices
            neighbours/3,               % +Vertex, +Graph, -Vertices
%           top_sort/2,                 % +Graph, -Sort
%           top_sort/3,                 % +Graph, -Sort0, -Sort
%           transitive_closure/2,       % +Graph, -Closure
            transpose_wgraph/2,         % +Graph, -NewGraph
            vertices/2,                 % +Graph, -Vertices
            vertices_edges_to_wgraph/3, % +Vertices, +Edges, -Graph
            wgraph_union/3              % +Graph1, +Graph2, -Graph
]).


:- use_module(library(lists), [
        append/3,
        member/2
   ]).


:- use_module(library(ordsets), [
        ord_add_element/3,
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

vertices([], []) :- !.
vertices([Vertex-_|Graph], [Vertex|Vertices]) :-
    vertices(Graph, Vertices).


%!  vertices_edges_to_wgraph(+Vertices, +Edges, -WGraph) is det.
%
%   Create a WGraph from Vertices and edges.   Given  a graph with a
%   set of Vertices and a set of   Edges,  Graph must unify with the
%   corresponding S-representation. Note that   the vertices without
%   edges will appear in Vertices but not  in Edges. Moreover, it is
%   sufficient for a vertex to appear in Edges.
%
%   ==
%   ?- vertices_edges_to_wgraph([],[1-3-0.5,2-4-2.0,4-5-1.2,1-5-4.0], L).
%   L = [1-[3-0.5,5-4.0], 2-[4-2.0], 3-[], 4-[5-1.2], 5-[]]
%   ==

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


%!  add_vertices(+Graph, +Vertices, -NewGraph) is det.
%
%   Unifies Newgraph with a new graph by adding the list of Vertices to
%   to Graph.

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
    edges_vertices_subtract(Edges, V1, NEdges),
    del_remaining_edges_for_vertices(G, V1, NG).


split_on_del_vertices(<, V, Edges, Vs, Vs, V1, [V-NEdges|NG], NG) :-
    edges_vertices_subtract(Edges, V1, NEdges).
split_on_del_vertices(>, V, Edges, [_|Vs], Vs, V1, [V-NEdges|NG], NG) :-
    edges_vertices_subtract(Edges, V1, NEdges).
split_on_del_vertices(=, _, _, [_|Vs], Vs, _, NG, NG).


%!  edges_vertices_subtract(+Edges, +Vertices, -NewEdges)
%   NewEdges contains all Edges that don't contain any of Vertices.

edges_vertices_subtract([], _Not, []).
edges_vertices_subtract([H1|T1], L2, Diff) :-
    diff21(L2, H1, T1, Diff).


diff21([], H1-W1, T1, [H1-W1|T1]).
diff21([H2|T2], H1-W1, T1, Diff) :-
    compare(Order, H1, H2),
    diff3(Order, H1-W1, T1, H2, T2, Diff).


diff12([], _H2, _T2, []).
diff12([H1-W1|T1], H2, T2, Diff) :-
    compare(Order, H1, H2),
    diff3(Order, H1-W1, T1, H2, T2, Diff).


diff3(<,  H1-W1, T1,  H2, T2, [H1-W1|Diff]) :-
    diff12(T1, H2, T2, Diff).
diff3(=, _H1, T1, _H2, T2, Diff) :-
    edges_vertices_subtract(T1, T2, Diff).
diff3(>,  H1-W1, T1, _H2, T2, Diff) :-
    diff21(T2, H1-W1, T1, Diff).


%!  add_edges(+Graph, +Edges, -NewGraph)
%
%   NewGraph is Graph with Edges added.

add_edges(Graph, Edges, NewGraph) :-
    p_to_s_graph(Edges, G1),
    wgraph_union(Graph, G1, NewGraph).


p_to_s_graph(P_Graph, S_Graph) :-
    sort(P_Graph, EdgeSet),
    p_to_s_vertices(EdgeSet, VertexBag),
    sort(VertexBag, VertexSet),
    p_to_s_group(VertexSet, EdgeSet, S_Graph).


%!  wgraph_union(+Set1, +Set2, ?Union)
%
%   Is true when Union is the union of Set1 and Set2. This code is a
%   copy of set union

wgraph_union(Set1, [], Set1) :- !.
wgraph_union([], Set2, Set2) :- !.
wgraph_union([Head1-E1|Tail1], [Head2-E2|Tail2], Union) :-
    compare(Order, Head1, Head2),
    wgraph_union(Order, Head1-E1, Tail1, Head2-E2, Tail2, Union).


wgraph_union(=, Head-E1, Tail1, _-E2, Tail2, [Head-Es|Union]) :-
    ord_union(E1, E2, Es),
    wgraph_union(Tail1, Tail2, Union).
wgraph_union(<, Head1, Tail1, Head2, Tail2, [Head1|Union]) :-
    wgraph_union(Tail1, [Head2|Tail2], Union).
wgraph_union(>, Head1, Tail1, Head2, Tail2, [Head2|Union]) :-
    wgraph_union([Head1|Tail1], Tail2, Union).


%!  del_edges(+Graph, +Edges, -NewGraph)
%
%   Remove Edges from Graph gives NewGraph.

del_edges(Graph, Edges, NewGraph) :-
    p_to_s_graph(Edges, G1),
    graph_subtract(Graph, G1, NewGraph).


%!  graph_subtract(+Set1, +Set2, ?Difference)
%
%   Is based on ord_subtract

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


%!  edges(+WGraph, -Edges) is det.
%
%   Edges is the set of edges in WGraph. Each edge is represented as
%   a pair From-To, where From and To are vertices in the graph.

edges(Graph, Edges) :-
s_to_p_graph(Graph, Edges).


s_to_p_graph([], []) :- !.
s_to_p_graph([Vertex-Neibs|G], P_Graph) :-
    s_to_p_graph(Neibs, Vertex, P_Graph, Rest_P_Graph),
    s_to_p_graph(G, Rest_P_Graph).


s_to_p_graph([], _, P_Graph, P_Graph) :- !.
s_to_p_graph([Neib-Weight|Neibs], Vertex, [Vertex-Neib-Weight|P], Rest_P) :-
    s_to_p_graph(Neibs, Vertex, P, Rest_P).


%!  neighbors(+Vertex, +Graph, -Neigbours) is det.
%!  neighbours(+Vertex, +Graph, -Neigbours) is det.
%
%   Neigbours is a sorted list of the neighbours of Vertex in Graph.

neighbors(Vertex, Graph, Neig) :-
    neighbours(Vertex, Graph, Neig).


neighbours(V,[V0-Nws|_],Nbs) :-
    V == V0,
    strip_neighbors(Nws, Nbs),   %% move cut before this?
    !.
neighbours(V,[_|G],Neig) :-
neighbours(V,G,Neig).


strip_neighbors([], []).
strip_neighbors([N-_|Nweights], [N|Nbs]) :-
    strip_neighbors(Nweights, Nbs).


%!  transitive_closure(+Graph, -Closure)
%
%   Closure is the transitive closure of Graph.

transitive_closure(Graph, Closure) :-
    false.


%!  transpose_wgraph(Graph, NewGraph) is det.
%
%   Unify NewGraph with a new graph obtained from Graph by replacing
%   all edges of the form V1-V2 by edges of the form V2-V1. The cost
%   is O(|V|*log(|V|)). Notice that an undirected   graph is its own
%   transpose. Example:
%
%     ==
%     ?- transpose([1-[3,5],2-[4],3-[],4-[5],
%                   5-[],6-[],7-[],8-[]], NL).
%     NL = [1-[],2-[],3-[1],4-[2],5-[1,4],6-[],7-[],8-[]]
%     ==

transpose_wgraph(Graph, NewGraph) :-
    edges(Graph, Edges),
    vertices(Graph, Vertices),
    flip_edges(Edges, TransposedEdges),
    vertices_edges_to_wgraph(Vertices, TransposedEdges, NewGraph).


flip_edges([], []).
flip_edges([Key-Val-Weight|Pairs], [Val-Key-Weight|Flipped]) :-
    flip_edges(Pairs, Flipped).


%!  compose(G1, G2, Composition)
%
%   Calculates the composition of two S-form  graphs, which need not
%   have the same set of vertices.

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


