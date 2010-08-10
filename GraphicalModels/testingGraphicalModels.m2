-- let's see what all the functions in the package are:
load "GraphicalModels.m2"
help GraphicalModels 
-- output:
-- * Functions
--           * "gaussIdeal" -- correlation ideal of a Bayesian network of joint Gaussian variables
--           * "gaussMinors"
--           * "gaussRing" -- ring of gaussian correlations on n random
--             variables
--           * "gaussTrekIdeal"
--y           * "globalMarkovStmts"
--?           * "hideMap"
--y           * "localMarkovStmts"
--?           * "marginMap"
--y           * "markovIdeal"
--y           * "markovMatrices"
--y          * "markovRing" -- ring of probability distributions on several discrete random variables
--y           * "pairMarkovStmts"
--removed!           * "removeRedundants"

-------------------------------------
-- make a graph and a digraph 
-- and test the functions on them:
-------------------------------------

--installPackage "Graphs"
--loadPackage "Graphs"
viewHelp "Graphs"
help graph
R=QQ[x_1,x_4]
A = graph({{x_1,x_3},{x_2,x_4},{x_1,x_4}})            
B = graph({{a,b},{c,d},{a,d},{b,c}}, Singletons => {f})
help digraph
D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}}, 
	  {f, {}}, {g, {}}, {h, {}}}) 

-------------------------------------
-- checking various markov statements:
-- note: all fixed to accept any type of graph, not just w/ integer nodes. 
-------------------------------------

-- testing function "globalMarkovStmts"
help globalMarkovStmts --no documentation
globalMarkovStmts D --fixed
load "GraphicalModels.m2"
Dint = digraph({{8, {7,6}}, {7,{5,4}}, {6, {4,1}}, {5, {3}}, {4, {3,2}}, 
	  {3, {}}, {2, {}}, {1, {}}}) 
globalMarkovStmts Dint --works for integer labels.

-- testing function "pairMarkovStmts"
pairMarkovStmts D --executed
pairMarkovStmts Dint --executed, comparison against Markov.m2 OK

-- testing function "localMarkovStmts"
localMarkovStmts D --executed
localMarkovStmts Dint --executed, comparison against Markov.m2 OK

--printWidth=200
--removeRedundants glo ----no longer exported!!!

-------------------------------------
-- TO DO:
-------------------------------------
--for all 3 above, need to work on "convertToIntegers(G)" 
--because the conversion does not make sense.
--ON TOP OF THAT: need to convert back from integers to the original labels!!!
-- SONJA: all this needs to do is a topological sort of the graph;
 --so, run DFS and sort the vertices in decr. order of finishing times. the lowest time vtx is the lowest label.
 -- the rule is this: if a is a descendent of b, then a has a lower integer label then b.

-------------------------------------
--THE FOLLOWING NEEDS TO GO TO Graphs.m2 :
-------------------------------------
--  pseudocode for topSort(G):
--call DFS(G) to compute finish times for each vertex v of G
--order finish times in decreasing order, i.e., as each vertex is finished, insert it at the front of a (linked)list.

--  pseudocode for DFS(G):
--for each vertex u in V(G) do: color(u)=white; parent(u)=Nil;
--time=0;
--for each vertex u do: if color(u)==white, then DFSvisit(u);

--  pseudocode for DFSvisit(u):
--color(u)=gray --vtx has just been discovered
--time = time+1
--d(u)=time
--for each v in Adjacent(u) do: --explore edge (u,v)
--     if color(v)==white then parent(v)=u; DFSvisit(v);
--color(u)=black --u is finished
--time=time+1
--finishTime(u)=time.
-------------------------------------

-- once that is done, the topSort will return the new type SortedDigraph. 
-- TO DO: change markov statements fns to map the integer labels back to original labels. 

-------------------------------------
-- testing function "markovRing", "markovIdeal", "markovMatrices":
-------------------------------------

help markovRing --doc there. comments: needs update?
R = markovRing(2,3,4,5) --ok
numgens R
R_0 --the first variable.

help markovMatrices --no doc.
L=localMarkovStmts(Dint)
d=toList(8:2)
R = markovRing(d)
M=markovMatrices(R,L);--it runs but it is huge! do not display

help markovIdeal --no doc.
--this just takes minors of the markovMatrices. as in the book :) 
I=markovIdeal(R,L);-- this works. it calls markovMatrices too.
-- THERE should be an option for passing markovMatrices to this method 
--so we don't recompute!
betti I



-------------------------------------
-- I have no idea what these do:
-------------------------------------

help hideMap --no doc. 
-- not used anywhere else.
-- @code:   -- creates a ring map inclusion F : S --> A.
     -- R should be a Markov ring
hideMap(1,R) --works but needs to be studied;

help marginMap --no doc.
marginMap(1,markovRing(2,3))-- this marginalizes the first variable, as expected :)
--this is supposed to be used to marginalize hidden vars!!

setit = (d) -> {set{d#0,d#1}, d#2}

under = (d) -> (
           d01 := toList d_0;
           d0 := toList d01_0;
           d1 := toList d01_1;
           d2 := toList d_1;
           e0 := subsets d0;
           e1 := subsets d1;
           z1 := flatten apply(e0, x -> apply(e1, y -> (
      		    {set{d01_0 - set x, d01_1 - set y}, set x + set y + set d_1})));--added "set" to d_1
           z2 := flatten apply(e0, x -> apply(e1, y -> (
      		    {set{d01_0 - set x, d01_1 - set y}, set d_1})));--added "set" to d_1
           z = join(z1,z2);
           z = select(z, z0 -> not member(set{}, z0_0));
           set z
           )
s=glo_0
under setit s
removeRedundants glo; ----NEED TO RUN THIS W/ UNDER CHANGED!!
break


loadPackage "GraphicalModels"
load "GraphicalModels.m2"
--- documentation notes:
help pairMarkovStmts
D = digraph({{a, {b,c}}, {b,{d,e}}, {c, {e,h}}, {d, {f}}, {e, {f,g}}, 	  {f, {}}, {g, {}}, {h, {}}}) 
pairMarkovStmts D
D = digraph {{a,{b,c}}, {b,{c,d}}, {c,{}}, {d,{}}}
L = pairMarkovStmts D

help localMarkovStmts
help globalMarkovStmts
help markovRing
help marginMap
help hideMap