-- -*- coding: utf-8 -*-
newPackage("Graphs",
     Authors => {
	  {Name => "Amelia Taylor"},
	  {Name => "Augustine O'Keefe"}
	  },
     ---- Also Doug Torrance.  --- clearly a current author.  Current role of Amelia and Tina?
     ---- Shaowei Lin and Alex Diaz contributed mixedGraph
     DebuggingMode => true,
     Headline => "Data types, visualization, and basic funcitons for graphs",
     Version => "0.1"
     )

export {Graph,
     Digraph,
     Bigraph,
     MixedGraph,
     LabeledGraph,
     graph,
     digraph,
     bigraph,
     mixedGraph,
     labeledGraph,
     Singletons,
     vertices,
     edges,
     descendents,
     nondescendents,
     parents,
     children,
     neighbors,
     nonneighbors,
     foreFathers,     
     displayGraph,
     showTikZ,
     simpleGraph,      
     removeNodes, 
     inducedSubgraph,
     completeGraph,
     cycleGraph,
     writeDotFile,
     SortedDigraph,
     topSort,
     DFS,
     isCyclic,
     adjacencyMatrix,
     degreeMatrix,
     laplacianMatrix,
     incidenceMatrix,
     pathConnected,
     adjacencyHashTable
     }
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

Bigraph = new Type of HashTable
     -- a bigraph is a hash table in the form { A => set {B,C, ...}, 
     -- where the set consists of the neighbors of A. This in only
     -- used in GraphicalModels and MixedGraph.  

MixedGraph = new Type of HashTable
     -- a mixed graph is a HashTable of Digraphs whose keys (vertex sets) are the same.
     
LabeledGraph = new Type of HashTable
   

digraph = method()
digraph HashTable := (g) -> (
     -- Input:  A hash table with keys the names of the nodes of 
     --         and the values the children of that node.      
     -- Output: A hash table of type Digraph.
     --         If a value of the hash table g is a List, Sequence or Array, it is converted into a set.
     --         If a value x of the hash table g is not a Set or VisibleList, it is converted into a set {x}.
     if g === (new HashTable) then new Digraph from g else (
     	  G := applyValues(g, x->if instance(x,VisibleList) then set x else if (class x) =!= Set then set {x} else x);
     	  nullVertices := toList (sum(values G) - keys G);
     	  new Digraph from merge(G,hashTable apply(nullVertices,i->{i,set {}}),plus)
     	  )
     )

digraph List := (g) -> (
     -- Input:  A list of pairs where the first element of the pair is the 
     --         name of a node and the second is the list of 
     --         children for that node. If a node has no children,
     --         then the second element of the pair should be empty. 
     -- Output:  A hashtable with keys the names of the nodes 
     --          with values the children.
     if g === {} then new Digraph from new HashTable else (
     	  G := apply(g, x->{x#0,if instance(x#1,VisibleList) then set x#1 else if (class x#1) =!= Set then set {x#1} else x#1});
     	  H := new MutableHashTable from apply(G,x->{x#0,set {}});     
     	  scan(G, x -> H#(x#0) = H#(x#0) + x#1);
     	  digraph (new HashTable from H)
	  )
     )
     
graph = method(Options => {Singletons => null})
graph HashTable := opts -> (g) -> (
     -- Input:  A hash table with keys the names of the nodes of 
     --         the graph and the values the neighbors of that node. 
     -- Output: A hash table of type Graph. 
     G := digraph g;
     -- make sure that for every edge A-B, B appears in the value of A and vice versa.
     if G === digraph({}) then new Graph from G else (
     	  H := new MutableHashTable from G;
     	  scan(keys G, i->scan(toList G#i, j-> H#j=H#j+set{i}));
     	  new Graph from H)
     )

graph List := opts -> (g) -> (
     -- Input:  A list of lists with two elements which describe the 
     --         edges of the graph. 
     -- Output:  A hash table with keys the names of the nodes and the 
     --          values are the neighbors corresponding to that node. 
     ---- Note to Selves --- this code should also nicely build
     ---- hypergraphs as hash tables with again, nodes as keys and
     ---- neighbors as values.
     G := digraph (g|if opts.Singletons === null then {} else apply(opts.Singletons,i->{i,{}}));
     -- make sure that for every edge A-B, B appears in the value of A and vice versa.
     if G === digraph({}) then new Graph from G else (
     	  H := new MutableHashTable from G;
     	  scan(keys G, i->scan(toList G#i, j-> H#j=H#j+set{i}));
     	  new Graph from H)
     )

bigraph = method()
bigraph HashTable := (g) -> (
     -- Input:  A hash table with keys the names of the nodes of 
     --         the graph and the values the neighbors of that node. 
     -- Output: A hash table of type Bigraph. 
     -- Caveat: The final object looks just like a Graph.  Thus the
     -- purpose of this code and the type Bigraph is to have clear
     -- constructions and interpretations in GraphicalModels. 
     G := digraph g;
     -- make sure that for every edge A-B, B appears in the value of A and vice versa.
     if G === digraph({}) then new Bigraph from G else (
     	  H := new MutableHashTable from G;
     	  scan(keys G, i->scan(toList G#i, j-> H#j=H#j+set{i}));
     	  new Bigraph from H)
     )

bigraph List := (g) -> (
     -- Input:  A list of lists with two elements which describe the 
     --         edges of the graph. 
     -- Output:  A hash table with keys the names of the nodes and the 
     --          values are the neighbors corresponding to that node. 
     -- Caveat: The final object looks just like a Graph.  Thus the
     -- purpose of this code and the type Bigraph is to have clear
     -- constructions and interpretations in GraphicalModels. 
     G := digraph g;
     -- make sure that for every edge A-B, B appears in the value of A and vice versa.
     if G === digraph({}) then new Bigraph from G else (
     	  H := new MutableHashTable from G;
     	  scan(keys G, i->scan(toList G#i, j-> H#j=H#j+set{i}));
     	  new Bigraph from H)
     )

------- Definitely need descendents.  

mixedGraph = method()
mixedGraph (Graph, Digraph, Bigraph) := (g,d,b) -> (
    -- Input: A hashtable of digraphs.
    -- Output: A hashtable of digraphs with the same vertex set,
    --         which is the union of the vertex sets of the input
    --         digraphs.
    if not instance(g, Graph) then error "expected first argument to be a Graph";
    if not instance(d, Digraph) then error "expected second argument to be a Digraph";
    if not instance(b, Bigraph) then error "expected third argument to be a Bigraph";
    h := new MutableHashTable;
    h#(class g) = g;
    h#(class d) = d;
    h#(class b) = b;
    new MixedGraph from h)

mixedGraph (Digraph, Bigraph) := (d,b) -> (
    -- Input: A hashtable of digraphs.
    -- Output: A hashtable of digraphs with the same vertex set,
    --         which is the union of the vertex sets of the input
    --         digraphs.
    mixedGraph(graph {},d,b))

mixedGraph (Graph, Digraph) := (g,d) -> (
    -- Input: A hashtable of digraphs.
    -- Output: A hashtable of digraphs with the same vertex set,
    --         which is the union of the vertex sets of the input
    --         digraphs.
    mixedGraph(g,d,bigraph {}))

mixedGraph (HashTable) := (d) -> (
    -- Input: A hashtable of digraphs.
    -- Output: A hashtable of digraphs with the same vertex set,
    --         which is the union of the vertex sets of the input
    --         digraphs.
    mixedGraph(graph {},d, bigraph {}))


--mixedGraph = method()
--mixedGraph HashTable := (g) -> (
    -- Input: A hashtable of digraphs.
    -- Output: A hashtable of digraphs with the same vertex set,
    --         which is the union of the vertex sets of the input digraphs.
--	scanKeys(g, i-> if not instance(g#i, Digraph) then error "expected HashTable of Digraphs");
--	vertices := toList sum(apply(keys(g),i->set keys(g#i)));
--	new MixedGraph from applyValues(g, i->(
--	  hh := new MutableHashTable;
--	  scan(vertices,j->if i#?j then hh#j=i#j else hh#j={});
--	  new class(i) from hh
--	))
--)     


labeledGraph = method()
labeledGraph (Digraph,List) := (g,L) -> (
     -- Input:  A graph and a list of lists with two elements one of
     --         which is a list giving an edge and the other is the labels. 
     --         The list of labels are of the form {{A,B},edgeName} for the directed edge A->B.
     --         For undirected graphs,  
     -- Output:  A list of two hash tables, the first of which is the
     --      	 base graph and the second of which has for keys edges of the
     --      	 graph whose values are the name of the edge.  
     ---- Note to Selves --- this code should also nicely build
     ---- hypergraphs as hash tables with again, nodes as keys and
     ---- neighbors as values. 
     lg := new MutableHashTable;
     lg#graphData = g;
     label := new MutableHashTable;
     if (class g) === Graph then (
       sg := simpleGraph g;
       scan(L, i -> (
  	 if (sg#(i#0#0))#?(i#0#1) then
	   label#(i#0) = i#1
	 else if (sg#(i#0#1))#?(i#0#0) then
	   label#({i#0#1,i#0#0}) = i#1
	 else
	   error (toString(i#0)|" is not an edge of the graph");
       ));
     ) else (
       scan(L, i -> (
	 if (g#(i#0#0))#?(i#0#1) then
	   label#(i#0) = i#1
	 else
	   error (toString(i#0)|" is not an edge of the graph");
       ));
     );
     lg#labels = new HashTable from label;
     new LabeledGraph from lg)

     
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
     new Digraph from hashTable pairH)


 
writeDotFile = method()
writeDotFile(String, Graph) := (filename, G) -> (
     -- Input: The desired file name for the DOT file created and a graph.
     -- Output: The code for the inputted graph to be constructed in Graphviz 
     --         with the specified file name.
     H := simpleGraph G;
     fil := openOut filename;
     fil << "graph G {" << endl;
     q := pairs H;
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

showTikZ = method(Options=>{Options=>"-t math --prog=dot -f tikz --figonly"})
showTikZ(Digraph) := opt -> G -> (
     dotfilename := temporaryFileName() | ".dot";
     writeDotFile(dotfilename,G);
     output := temporaryFileName();
     runcmd("dot2tex "|opt#Options|" "|dotfilename|" >> "|output);
     get output
     )

------------------
-- Graph basics --
------------------

vertices = method()
     -- Input: A digraph
     -- Output:  A list of vertices
vertices(Digraph) := G -> keys(G)    
vertices(MixedGraph) := G ->  toList sum(apply(keys(G),i->set keys(G#i)));

edges = method()
     -- Input: A graph
     -- Output: A list of sets of order 2, each corresponding to an edge
edges(Digraph) := G -> flatten apply(keys(G),i->apply(toList G#i,j->{i,j}))
edges(Graph) := G -> edges simpleGraph G 


descendents = method()
descendents(Digraph,Thing) := (G,v) -> (
     -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are descendents of the vertex 
     --         of interest.
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

--descendent(MixedGraph, Thing) := (G,v) -> (
    -- Input: A digraph and the key for the vertex of interest.
     -- Output: The set of vertices that are descendents of the vertex 
     --         of interest.
     
     
     
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
nonneighbors(Graph, Thing) := (G,v) -> set keys G - neighbors(G,v)-set{v}

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
adjacencyMatrix(Digraph) := G -> matrix apply(keys(G),i->apply(keys(G),j->#positions(toList G#i,k->k===j)))

adjacencyHashTable = method()
adjacencyHashTable (Digraph) := (G) -> (
    -- Input: A digraph G.
    -- Output: The hash table M of mutable hash tables storing the adjacency 
    --         matrix of G,where M#a#b is true if a->b, and false otherwise.

    vertices := keys G;
    hashTable apply(vertices, i->{i,hashTable apply(vertices,j->{j,#positions(toList G#i,k->k===j)})})
)

degreeMatrix = method()
degreeMatrix(Graph) := G -> matrix apply(#keys(G),i->apply(#keys(G),j->if i==j then #(G#((keys G)_i)) else 0))

laplacianMatrix = method()
laplacianMatrix(Graph) := G -> degreeMatrix G - adjacencyMatrix

incidenceMatrix = method()
     -- Input: A graph
     -- Output: A matrix M, such that M_(i,j)=1 iff vertex i is incident to edge j     
incidenceMatrix(Graph) := G -> matrix apply(keys(G),i->(apply(edges G,j->(if j#?i then 1 else 0))))

pathConnected = method()
pathConnected (Set,HashTable) := (A,M) -> (
    -- Input: A directed graph G and subset A of vertices.
    -- Output: Set of vertices of G which have a directed path from A.

    vertices := keys M;
    reachable := new MutableHashTable from apply(vertices,i->{i,false});
    queue := toList A;   
    while #queue > 0 do (
      topVertex := first queue;
      if not reachable#topVertex then (
        reachable#topVertex = true;
        queue = join(drop(queue,1),select(vertices,i->M#topVertex#i>0));
      ) else (
        queue = drop(queue,1);
      );
    );
    set select(vertices,i->reachable#i)
)

pathConnected (Set,Digraph) := (A,G) -> pathConnected(A,adjacencyHashTable G)

floydWarshall = method()
     -- Input:  A digraph
     -- Output:  A hash table whose keys are pairs of vertices and the value is the length of the shortest path between the first vertex and the second vertex
floydWarshall(Digraph) := G -> (
     D := new MutableHashTable from flatten apply(vertices(G),u->(apply(vertices(G),v->((u,v)=> if u===v then 0 else if member(v,(children(G,u))) then 1 else 1/0.))));
     scan(vertices(G),w->(
	       scan(vertices(G),u->(
			 scan(vertices(G),v->(
				   D#(u,v)=min(D#(u,v),D#(u,w)+D#(w,v))
				   )
			      )
			 )
		    )
	       )
	  );
     new HashTable from D
     )

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
     if not isCyclic G then (
     	  L := reverse apply(sort apply(pairs ((DFS G)#"finishingTime"),reverse),p->p_1);
     	  H := hashTable{
	       digraph => G,
	       newDigraph => digraph hashTable apply(#L,i->i+1=>apply(G#(L_i),j->position(L,k->k==j)+1)),
	       map => hashTable apply(#L,i->L_i => i+1)
	       };
     	  new SortedDigraph from H
	  )
     else error("digraph must be acyclic")
     )     

DFS = method()
     -- Input: A digraph
     -- Output: the discovery and finishing times for each vertex after a depth-first search
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
     new HashTable from {"discoveryTime" => new HashTable from H#d, "finishingTime" => new HashTable from H#f}
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

isCyclic = method()
     -- Input:  A digraph (not undirected)
     -- Output:  Whether the digraph contains a cycle
     -- uses Cormen Lemma 22.11 and Exercise 22.3-4
isCyclic(Digraph) := G -> (
     if class G === Graph then error ("must be a digraph") else (
     	  D := DFS G;
     	  member(true,flatten unique apply(select(keys G,u->#children(G,u)>0),u->(
	       	    	 apply(children(G,u),v->(
		    	      	   L := {D#"discoveryTime"#v,D#"discoveryTime"#u,D#"finishingTime"#u,D#"finishingTime"#v};
     	       	    	      	   L == sort L
		    	      	   )
	       	    	      )
	       	    	 )
     	       	    )
     	       )
     	  )
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
      functions to view graphs and digraphs.  These functions call the programs
      Graphviz and dot2tex and is only set up to function on Unix-like computers (e.g., Macintosh, Linux) at
      this time. 
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


doc ///
         Key
	      (adjacencyMatrix,Digraph)
	      adjacencyMatrix
         Headline
	      Computes the adjacency matrix of a graph or digraph
         Usage
	      M = adjacencyMatrix(G)
         Inputs
	      G:Digraph
         Outputs
	      M:Matrix
	      	    whose (i,j)-entry is 1 if ij is an edge or arc of G and 0 otherwise
         Description
            Text
	    	 Compute the adjacency matrix of the complete graph K_5.
            Example
	    	 adjacencyMatrix completeGraph 5
      ///

doc ///
         Key
	      (showTikZ,Digraph)
	      showTikZ
         Headline
	      outputs TikZ syntax for displaying a graph or digraph in TeX
         Usage
	      showTikZ G
         Inputs
	      G:Digraph
         Outputs
	      S:String
	      	    TikZ syntax which can be pasted into a .tex file to display G
         Description
            Text
	    	 showTikZ requires the external program dot2tex, available at http://www.fauskes.net/code/dot2tex/.
		 
		 The following code gives TikZ syntax for the complete graph K_5.
            Example
     	       	 showTikZ completeGraph 5
      ///
      
doc ///
        Key
	     [showTikZ,Options]
        Headline
	     a string which is passed to dot2tex.  Defaults to "-t math --prog=dot -f tikz --figonly".  Run "dot2tex --help" for all possibilties.
        Usage
	     foo
	Inputs
	     S:String     
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

restart
loadPackage"Graphs"

TEST /// ---- family members, neighbors and non-neighbors. 
G = graph({{a,b},{b,c},{a,c},{c,d}}, Singletons => {e})
H = digraph{{a,{b,c}},{b,{c,d}},{c,{d}},{c,{}}}
assert(neighbors(G,a) === set {b,c})
assert(nonneighbors(G,b) === set {d,e})
assert(parents(H,a) === set {})
assert(parents(H,c) === set {a,b})
assert(children(H,a) === set {b,c})
assert(descendents(H,a) === set {b,c,d})
assert(nondescendents(H,c) === set {a,b})
assert(foreFathers(H,c) === set {a,b})
///

TEST /// ---- display?

///

TEST /// ---- Functions on Graphs. 

///



     mixedGraph, labeledGraph, displayGraph,
     simpleGraph, removeNodes, inducedSubgraph, completeGraph,
     cycleGraph, writeDotFile, SortedDigraph, topSort, DFS,
     adjacencyMatrix, edgeSet, incidenceMatrix}
exportMutable {dotBinary,jpgViewer 

break
