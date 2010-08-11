-- -*- coding: utf-8 -*-
newPackage("Graphs",
     Authors => {
	  {Name => "Amelia Taylor"},
	  {Name => "Augustine O'Keefe"}
	  },
     ---- Also Doug Torrance.  Current role of Amelia and Tina?
     DebuggingMode => true,
     Headline => "Data types, visualization, and basic funcitons for graphs",
     Version => "0.1"
     )

export {Graph, Digraph, MixedGraph, LabeledGraph, graph, digraph, mixedGraph, labeledGraph, Singletons, descendents, nondescendents, 
     parents, children, neighbors, nonneighbors, foreFathers, displayGraph,
     simpleGraph, removeNodes, inducedSubgraph, completeGraph,
     cycleGraph, writeDotFile,SortedDigraph,topSort,DFS,adjacencyMatrix,
     edgeSet,incidenceMatrix}
exportMutable {dotBinary,jpgViewer}


------------------------------------------------
-- Set graph types and constructor functions. -- 
------------------------------------------------

-- Give a graph as a hash table i => children for DAG and neighbors 
--                                   for undirected graphs. 

Digraph = new Type of HashTable
     -- a directed graph is a hash table in the form:
     -- { A => set {B,C,...}, ...}, where there are edges A->B, A->C, ...
     -- and A,B,C are symbols or integers. 

Graph = new Type of Digraph   
     -- an undirected graph is a hash table in the form:
     -- { A => set {B,C, ...}, where the set consists of 
     -- the neighbors of A. OR it is the neighbors for that 
     -- edge that are not a key earlier in the hash table. This 
     -- version removes the redunancy of each edge appearing twice. 
     -- simpleGraph is an internal conversion function. 

MixedGraph = new Type of HashTable
     -- a mixed graph is a HashTable of Digraphs whose keys (vertex sets) are the same.
     
LabeledGraph = new Type of Graph 
   

union := S -> (
     -- Input:  A list of lists of sets, in particular the list of the
     --         sets of individual neighbors of nodes, and the position of
     --         a particular node.
     -- Output:  A set of all the neighbors of a particular node.
     x = new MutableHashTable;
     for t in S do scanKeys(t, z -> x#z = 1);
     new Set from x)  

graph = method(Options => {Singletons => null})
graph List := opts -> (g) -> (
     -- Input:  A list of lists with two elements which describe the 
     --         edges of the graph. 
     -- Output:  A hash table with keys the names of the nodes and the 
     --          values are the neighbors corresponding to that node. 
     ---- Note to Selves --- this code should also nicely build
     ---- hypergraphs as hash tables with again, nodes as keys and
     ---- neighbors as values. 
     h := new MutableHashTable;
     vertices := toList set flatten g;
     if opts.Singletons === null then (
	  neighbors := for j to #vertices-1 list( 
	       for k to #g-1 list (if member(vertices#j, set g#k) 
		    then set g#k - set {vertices#j} 
		    else continue)
	       );
	  neighbors = apply(neighbors, i -> union i);
	  )
     else (vertices = join(vertices, opts.Singletons);
	  newEdges := apply(for i to #opts.Singletons - 1 list {}, i -> set i);
	  neighbors = for j to #vertices-1 list( 
	       for k to #g-1 list (if member(vertices#j, set g#k) 
		    then set g#k - set {vertices#j} 
		    else continue)
	       );
	  neighbors = apply(neighbors, i -> union i);
	  neighbors = join(neighbors,newEdges);
	  );
     apply(#vertices, i -> h#(vertices#i) = neighbors#i);
     new Graph from h
     )

mixedGraph = method()
mixedGraph HashTable := (g) -> (
    -- Input: A hashtable of digraphs.
    -- Output: A hashtable of digraphs with the same vertex set,
    --         which is the union of the vertex sets of the input digraphs.
	scanKeys(g, i-> if not instance(g#i, Digraph) then error "expected HashTable of Digraphs");
	vertices := toList sum(apply(keys(g),i->set keys(g#i)));
	new MixedGraph from applyValues(g, i->(
	  hh := new MutableHashTable;
	  scan(vertices,j->if i#?j then hh#j=i#j else hh#j={});
	  new class(i) from hh
	))
)     

labeledGraph = method()
labeledGraph (Digraph,List) := (g,L) -> (
     -- Input:  A graph and a list of lists with two elements one of
     --         which is a list giving an edge and the other is the lables. 
     -- Output:  A list of two hash tables, the first of which is the
     --      	 base graph and the second of which has for keys edges of the
     --      	 graph whose values are the name of the edge.  
     ---- Note to Selves --- this code should also nicely build
     ---- hypergraphs as hash tables with again, nodes as keys and
     ---- neighbors as values. 
     lg := new MutableHashTable;
     lg#graphData = g;
     label := new MutableHashTable;
     apply(L, i -> label#(i#0) = i#1);	   
     lg#labels = new HashTable from label;
     new LabeledGraph from lg
     )


--graph MutableHashTable := opts -> (g) -> (
--     new Graph from h)

graph HashTable := opts -> (g) -> (
     -- Input:  A hash table with keys the names of the nodes of 
     --         the graph and the values the neighbors of that node. 
     -- Output: A hash table of type Graph. 
     new Graph from g)

digraph = method()
digraph List := (g) -> (
     -- Input:  A list of pairs where the first element of the pair is the 
     --         name of a node and the second is the list of 
     --         children for that node. If a node has no children,
     --         then the second element of the pair should be empty. 
     -- Output:  A hashtable with keys the names of the nodes 
     --          with values the children.
     h := new MutableHashTable;
     scan(#g, i -> h#(g#i#0) = set g#i#1);
     new Digraph from h)
     

digraph HashTable := (g) -> (
     -- Input:  A hash table with keys the names of the nodes of 
     --         and the values the children of that node. 
     -- Output: A hash table of type Diraph. 
     new Digraph from g)
     
-----------------------------
-- Graph Display Functions --
-----------------------------

-- dotBinary = "/sw/bin/dot"
dotBinary = "dot"
-- jpgViewer = "/usr/bin/open"
jpgViewer = "open"

simpleGraph = method()
simpleGraph(Graph) := H -> (
     -- Input: A Graph.
     -- Output: A new Graph in which the keys are still the nodes but
     --         the values are the lists of neighbors so that if an
     --         edge has already appeared before, it will not appear again.
     pairH := new MutableList from pairs H;
     for k from 1 to #pairH-1 do (
	  testVertices := set for i to k-1 list pairH#i#0;
      	  pairH#k = (pairH#k#0, pairH#k#1-testVertices)
	  );
     new Graph from hashTable pairH)


 
writeDotFile = method()
writeDotFile(String, Graph) := (filename, G) -> (
     -- Input: The desired file name for the DOT file created and a graph.
     -- Output: The code for the inputted graph to be constructed in Graphviz 
     --         with the specified file name.
     G = simpleGraph G;
     fil := openOut filename;
     fil << "graph G {" << endl;
     q := pairs G;
     for i from 0 to #q-1 do (
	  e := q#i;
	  fil << "  \"" << toString e#0 << "\""; -- number of spaces added before the node is arbitrary
	  if #e#1 === 0 or all(q, j->member(e#0,j#1)) then
	    fil << ";" << endl
	  else (
	    fil << " -- {";
	    links := toList e#1;
	    for j from 0 to #links-1 do
		 fil << "\"" << toString links#j << "\";";
     	    fil << "};" << endl;
	    )
	  );
     fil << "}" << endl << close;
     )



writeDotFile(String, Digraph) := (filename, G) -> (
     -- Input:  The desired file name for the Dot file created and a digraph
     -- Output:  The code for the inputted digraph to be constructed in Graphviz 
     --          with the specified file name.
     fil := openOut filename;
     fil << "digraph G {" << endl;
     q := pairs G;
     for i from 0 to #q-1 do (
	  e := q#i;
	  fil << "  \"" << toString e#0 << "\"";
	  if #e#1 === 0 then
	    fil << ";" << endl
	  else (
	    fil << " -> {";
	    links := toList e#1;
	    for j from 0 to #links-1 do
		 fil << "\"" << toString links#j << "\";";
     	    fil << "};" << endl;
	    )
	  );
     fil << "}" << endl << close;
     )

runcmd := cmd -> (
     stderr << "--running: " << cmd << endl;
     r := run cmd;
     if r != 0 then error("--command failed, error return code ",r);
     )

displayGraph = method()
    -- Displays a graph or digraph using Graphviz
    -- Input:  A digraph or graph and optionally names for the dot
    --         and jpg files.
displayGraph(String,String,Digraph) := (dotfilename,jpgfilename,G) -> (
     writeDotFile(dotfilename,G);
     runcmd(dotBinary | " -Tjpg "|dotfilename | " -o "|jpgfilename);
     runcmd(jpgViewer | " " | jpgfilename);
     )
-- Note, when specifying a jpgfilename w/o the .jpg extension the
-- graph opens in Quicktime player.  Otherwise the graph opens in
-- Preview.  Why?  Does this matter? -T.O.
displayGraph(String,Digraph) := (dotfilename,G) -> (
     jpgfilename := temporaryFileName() | ".jpg";
     displayGraph(dotfilename,jpgfilename,G);
     --removeFile jpgfilename;
     )
displayGraph Digraph := (G) -> (
     dotfilename := temporaryFileName() | ".dot";
     displayGraph(dotfilename,G);
     --removeFile dotfilename;
     )

------------------
-- Graph basics --
------------------


descendents = method()
     -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are descendents of the vertex 
     --         of interest.
descendents(Digraph,Thing) := (G,v) -> (
     -- returns a set of vertices
     notDone := true;
     cC := children(G,v);
     dE := cC;
     while notDone === true do(
	  if (toList cC) === {} then notDone = false
	  else (
	       cC = set flatten apply(toList cC, i -> toList children(G,i));
	       dE = dE + cC;
	       )
	  );
     dE)
     
     
--     result := G#v;
--     scan(keys(G), i -> (
--	  if member(i,result) then result = result + G#i;
--     ));
--     result)


nondescendents = method()
     -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are not descendents of 
     --	        the vertex of interest.
nondescendents(Digraph,Thing) := (G,v) -> set keys G - descendents(G,v) - set {v}

parents = method()
     -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are the parents of the vertex 
     --	    	of interest.
parents(Digraph,Thing) := (G,v) -> set select(keys(G), i -> member(v,
G#i))

foreFathers = method()
     -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are the ancestors of the vertex 
     --	    	of interest.
foreFathers(Digraph, Thing) := (G,v) -> (
     notDone := true;
     cP := parents(G,v);
     aN := cP;
     while notDone === true do(
	  if (toList cP) === {} then notDone = false
	  else (
	       cP = set flatten apply(toList cP, i -> toList parents(G,i));
	       aN = aN + cP;
	       )
	  );
     aN)	  

children = method()
     -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are the children of the vertex 
     --	    	of interest.
children(Digraph,Thing) := (G,v) -> G#v

neighbors = method()
     -- Input: A graph and the key for the vertex of interest.
     -- Output: The set of vertices that are neighbors of the vertex 
     --	    	of interest.
neighbors(Graph,Thing) := (G,v) -> G#v  

nonneighbors = method()
     -- Input: A graph and the key for the vertex of interest.
     -- Output: The set of vertices that are not neighbors of the vertex 
     --	    	of interest.
nonneighbors(Graph, Thing) := (G,v) -> keys G - neighbors(G,v)-set{v}

removeNodes = method()
     -- Input: A digraph and the list of nodes you want to remove.
     -- Output: The digraph induced by removing the specified nodes
     --         and all edges incident to those nodes.
removeNodes(Digraph,List) := (G,v) -> (
     v = set v;
     G = select(pairs G, x -> not member(x#0,v));
     G = apply(G, x -> (x#0, x#1 - v));
     new Digraph from G
     )
--removeNodes(Digraph,ZZ) := (G,v) -> removeNodes(G, {v})

inducedSubgraph = method()
     -- Input: A digraph and the list of nodes you want to keep.
     -- Output: The digraph induced by keeping the specified nodes and 
     --         all edges whose endpoints are in the specified list.
inducedSubgraph(Digraph, List) := (G,v) -> (
     G = removeNodes(G,toList(keys(G)-set v));
     new Digraph from G
     )

adjacencyMatrix = method()
     -- Input:  A digraph
     -- Output:  A matrix M, such that M_(i,j)=1 iff there exists an arc from i to j
adjacencyMatrix(Digraph) := G -> matrix apply(keys(G),i->apply(keys(G),j->#positions(G#i,k->k===j)))

adjacencyHashTable = method()
adjacencyHashTable Digraph := (G) -> (
    -- Input: A digraph G.
    -- Output: The hash table M of mutable hash tables storing the adjacency 
    --         matrix of G,where M#a#b is true if a->b, and false otherwise.

    vertices := keys G;
    hashTable apply(vertices, i->{i,new MutableHashTable from apply(vertices,j->{j,#positions(G#i,k->k===j)})})
)

edgeSet = method()
     -- Input: A graph
     -- Output: A list of sets of order 2, each corresponding to an edge
edgeSet(Graph) := G -> unique flatten apply(keys(G),i->apply(#G#i,j->set{i,(elements G#i)_j}))

incidenceMatrix = method()
     -- Input: A graph
     -- Output: A matrix M, such that M_(i,j)=1 iff vertex i is incident to edge j     
incidenceMatrix(Graph) := G -> matrix apply(keys(G),i->(apply(edgeSet G,j->(if j#?i then 1 else 0))))

----------------------
-- Topological Sort --
----------------------

SortedDigraph = new Type of HashTable
     -- 3 keys:
     -- digraph: original digraph
     -- newDigraph: digraph with vertices labeled as integers obtained from sorting
     -- map: gives sorted order
     
-- functions adapted from pseudocode given in Cormen, Introduction to algorithms --

topSort = method()
     -- Input: A digraph
     -- A sorted digraph, topologically sorted
topSort(Digraph) := G -> (
     L := reverse apply(sort apply(pairs DFS G,reverse),p->p_1);
     H := hashTable{
	  digraph => G,
	  newDigraph => digraph hashTable apply(#L,i->i+1=>apply(G#(L_i),j->position(L,k->k==j)+1)),
	  map => hashTable apply(#L,i->L_i => i+1)
	  };
     new SortedDigraph from H
     )     

DFS = method()
     -- Input: A digraph
     -- Output: the finishing times for each vertex after a depth-first search
DFS(Digraph) := G -> (
     H := new MutableHashTable;
     H#graph = G;
     H#color = new MutableHashTable;
     H#p = new MutableHashTable;
     H#d = new MutableHashTable;
     H#f = new MutableHashTable;
     H#t = 0;
     scan(keys(G),u->(H#color#u="white";H#p#u=nil));
     scan(keys(G),u->if H#color#u == "white" then H = DFSvisit(H,u));
     H#f
     )

DFSvisit = (H,u) -> (
     H#color#u = "gray";
     H#t = H#t+1;
     H#d#u = H#t;
     scan(children(H#graph,u),v->if H#color#v == "white" then (H#p#v = u;H = DFSvisit(H,v)));
     H#color#u = "black";
     H#t = H#t+1;
     H#f#u = H#t;
     H
     )

-------------------
-- Common Graphs --
-------------------


completeGraph = method()
     -- Input: a positive integer n
     -- Output: the complete graph on n nodes labeled 0 through n-1
completeGraph(ZZ) := n -> (
      i:= 0;
      G := new MutableHashTable;
      L := while i < n list i do i = i+1;
      apply(L, i-> G#i =  set L - set {i});
      G = graph(G)
      )   

cycleGraph = method()
     -- Input: a positive integer n
     -- Output: the cyclic graph on n nodes labeled 0 through n-1 
cycleGraph(ZZ) := n -> (
     i := 0;
     G := new MutableHashTable;
     while i < n do(
	  G#i = set{(i-1)%n,(i+1)%n}; 
	  i = i+1;
	  );
     G = graph(G)
     )
  

--------------------
-- Documentation  --
--------------------


///
restart
loadPackage "Graphs"
A = graph({{a,b},{c,d},{a,d},{b,c}}, Singletons => {f})
B = digraph({{a,{b,d}},{b,{c}},{d,{a,c}}})
C = digraph({{a,{b,c}}, {b,{d}}, {c,{}}, {d,{}}})
H = digraph({{a,{d,f}}, {d,{h,e}}, {f,{e,c}}, {h,{g}}, {e,{g,b}}, {g,{}}, {b,{}}, {c,{}}})
inducedSubgraph(H,{a,f,h,g})
K = graph({{a,b},{b,c},{c,d},{d,e},{a,e},{b,e}})
inducedSubgraph(K,{a,e,b})
///



beginDocumentation()

doc ///
  Key
    Graphs
  Headline
    Data types and basic functions on graphs used in algebra and algebraic geometry. 
  Description
    Text
      This package is used to construct digraphs and graphs and
      perform basic functions on them. The user should note that this
      package assumes that all digraphs are acyclic.  Also, graphs are 
      assumed to have no loops or multiple edges. This package has
      functions to view graphs and digraphs.  These functions call the program
      Graphviz and is only set up to function on Macintosh computers, at
      this time. 
  Caveat
    When asked to display a graph, this package converts the way M2 
    stores information for a graph into a format readable by the 
    external software Graphviz.  The way in which this is currently
    done does not support node names that include superscripts or 
    subscripts.
///

doc ///
  Key
    Graph
  Headline
    The data type for an undirected graph
  Description
    Text    
///

doc ///
  Key
    Digraph
  Headline
    The data type for a directed graph
  Description
    Text
///

doc ///
  Key
    graph
  Headline
    The function that creates a graph
  Usage
    G = graph(L) or G = graph(L, Singletons => K) or G = graph(H)
  Inputs
    L:List 
      of edges of the graph
    K:List 
      of isolated nodes of the graph
    H:HashTable 
      whose keys are the nodes of the graphs and whose values are the
      neighbors of the nodes
  Outputs
    G:Graph
  Description
    Text
      The graph is stored as a hash table whose keys are the nodes and
      whose values are the neighbors of the nodes.  The user inputs a
      graph by inputting a list of edges. There is an optional
      argument called Singletons to input nodes that have no neighbors. 
    Example
      A = graph({{x_1,x_3},{x_2,x_4},{x_1,x_4}})
      B = graph({{a,b},{c,d},{a,d},{b,c}}, Singletons => {f})
    Text  
      Alternatively, one can also create a graph by inputting a hash
      table whose keys are again the nodes of the graph and the values
      the neighbors of the nodes.
///



doc ///
  Key
    digraph
  Headline
    The function that creates a digraph
  Usage
    D = digraph(L) or D = digraph(H)
  Inputs
    L:List
      of pairs consisting of a node and its children
    H:HashTable
      whose keys are the nodes of the digraph and whose values are the
      children of the nodes
  Outputs
    D:Digraph
  Description
    Text
      The digraph is stored as a hash table whose keys are the names
      of the nodes and whose values are the children of those nodes.
      The user inputs a digraph by inputting a list of pairs whose first
      element is a node and whose second element is the list of children
      of that node.  If a node has no children, it should still be
      included in the list of pairs followed by an empty list.
      Alternatively, one could also input a hash table where the keys are
      the nodes and the values the set of children.
    Example
      D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}},
  	  {f, {}}, {g, {}}, {h, {}}})
///



doc ///
  Key
    Singletons
  Headline
    Optional argument for the function graph
  Description
    Text
      This is an optional argument for @TO graph@ to input a list of nodes
      with no neighbors.
  
///

doc ///
  Key
    descendents
  Headline 
    Returns the descendents of a node in a digraph
  Usage
    dE = descendents(D,v)
  Inputs
    D:Digraph
    v:Thing
      representing a node in the digraph
  Outputs
    dE:Set
       consisting of the descendents of v.
  Description
    Text
      This is a function which takes as input a @TO digraph@ and the key
      from its hash table for the node of interest.  It returns a set 
      of the keys for the descendents of that node.
    Example
      D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}},
  	  {f, {}}, {g, {}}, {h, {}}})
      dE = descendents(D,c)
///



doc ///
  Key
    nondescendents
  Headline
    Returns the nondescendents of a node in a digraph
  Usage
    nD = nondescendents(D,v)
  Inputs
    D:Digraph
    v:Thing
      representing a node in the digraph
  Outputs
    nD:Set
       consisting of the nondescendents of v. 
  Description
    Text
      This function takes as input a @TO digraph@ and the name given
      to the node of interest.  It returns the set of vertices that
      are not descendents of that node.
    Example
      D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}},
  	  {f, {}}, {g, {}}, {h, {}}})
      nD = nondescendents(D,c)
///



doc ///
  Key
    parents
  Headline
    Returns the parents of a vertex in a digraph
  Usage
    pA = parents(D,v)
  Inputs
    D:Digraph
    v:Thing
      that is the name of the node of interest
  Outputs
    pA:Set
       containing the names of the parents of the node
  Description
    Text
      This function takes as input a @TO digraph@ and the name of
      the node of interest.  It returns the set of the names
      for the vertices that are the parents of the node given.
    Example
      D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}},
  	  {f, {}}, {g, {}}, {h, {}}})
      pA = parents(D,e)
///

doc ///
  Key
    children
  Headline
    Returns the children of a node in a digraph
  Usage
    cH = children(D,v)
  Inputs
    D:Digraph
    v:Thing
      that is the name of the node of interest
  Outputs
    cH:Set
       containing the names of the children of the node
  Description
    Text
       This function takes as input a @TO digraph@ and the name of 
       the node of interest.  This function returns the set of the names
       for the vertices that are the children of the node given. 
    Example
      D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}},
  	  {f, {}}, {g, {}}, {h, {}}})
      cH = children(D,e)
///
end

doc ///
  Key
    neighbors
  Headline
    Returns the neighbors of a given node in a graph or digraph. 
  Usage
  Inputs
  Outputs
  Description
    Text
///

end

doc ///
  Key
    nonneighbors
  Headline
  Description
    Text
///

doc ///
  Key
    displayGraph
  Headline
  Description
    Text
///

doc ///
  Key
    simpleGraph
  Headline
  Description
    Text
///

doc ///
  Key
    removeNodes
  Headline
  Description
    Text
///

doc ///
  Key
    dotBinary
  Headline
  Description
    Text
///

doc ///
  Key
    jpgViewer
  Headline
  Description
    Text
///

end


break
