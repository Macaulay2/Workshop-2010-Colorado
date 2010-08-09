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
--           * "markovIdeal"
--           * "markovMatrices"
--ok          * "markovRing" -- ring of probability distributions on several discrete random variables
--y           * "pairMarkovStmts"
--           * "removeRedundants"

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
-------------------------------------

-- testing function "globalMarkovStmts"
help globalMarkovStmts --no documentation
globalMarkovStmts D --broken: error at line 314;
convertToIntegers --this is line 313 and it makes no sense.  the fn itself is line 96:
--Now, with line 313 commented out, and the equivalent graph given with integer labels, let's run it:
load "GraphicalModels.m2"
Dint = digraph({{8, {7,6}}, {7,{5,4}}, {6, {4,1}}, {5, {3}}, {4, {3,2}}, 
	  {3, {}}, {2, {}}, {1, {}}}) 
globalMarkovStmts Dint --works for integer labels.
--let's put line 313 back and run it:
globalMarkovStmts D --executed. 
globalMarkovStmts Dint --executed, comparison against Markov.m2 OK

-- testing function "pairMarkovStmts"
pairMarkovStmts D --executed
pairMarkovStmts Dint --executed, comparison against Markov.m2 OK

-- testing function "localMarkovStmts"
localMarkovStmts D --executed
localMarkovStmts Dint --executed, comparison against Markov.m2 OK

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


-------------------------------------
-- testing function "markovRing", "markovIdeal", "markovMatrices":
-------------------------------------

help markovRing --doc there. comments: needs update?
R = markovRing(2,3,4,5) --ok
numgens R
R_0 --the first variable.

help markovIdeal --no doc.

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


