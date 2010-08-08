-- -*- coding: utf-8 -*-

needsPackage"Graphs"

newPackage(
     "GraphicalModels",
     Version => "1.2",
     Authors => {
	  {Name => "Luis Garcia"},
	  {Name => "Mike Stillman"}
	  },
     Headline => "Markov ideals, arising from Bayesian networks in
     statistics",
     DebuggingMode => true
     )

---- 28.10.09 ---- 
---- Version by the Working group at Aim  and MSRI
---- Amelia Taylor and Augustine O'Keefe
---- Comments from this group have 4 dashes, those with 2 are Mike/Luis. 


------------------------------------------
-- markov ideals in Macaulay2
-- Authors: Luis Garcia and Mike Stillman
-- 
-- Routines:
--   makeGraph {{},{1},{1},{2,3},{2,4}}
--   displayGraph(name,G)
--
--   localMarkovStmts G -- G is a directed graph
--   globalMarkovStmts G
--   pairMarkovStmts G
--
--   markovRing (2,2,3,3)
--
--   marginMap(R,i) : R --> R
--   hiddenMap(R,i) : R --> S
--
--   markovMatrices S  -- S is a list of independence statements
--   markovIdeal S
--
-- For examples of use, see the 
------------------------------------------


export {localMarkovStmts, globalMarkovStmts, pairMarkovStmts,
       markovRing, marginMap, hideMap, markovMatrices, markovIdeal, removeRedundants, 
       gaussRing, gaussMinors, gaussIdeal, gaussTrekIdeal}
     
needsPackage"Graphs"

---- List from Board at AIM.

---- a)  Discrete   b) Gaussian
----
---- (0) CI models   (3.1) 
---- (1) Undirected Graph  (3.2)
---- (2) DAG    (3.2) 
---- (3) Chain Graphs (DAG & undirected)   (3.2)
----
----  Local and Global Markov properties  (3.2)
----  use, when appropriate thms that say local <=> global based on conditions
----  
----  parametrizations and for toric varieties the the corresponding matrix. 
----  In the case of toric varieties the matrix is easy.  Here is the code, 
----  commented out to be used later when we are ready. 
---- 
----  toAMatrix = method()
----  toAMatrix List := Matrix => (M) -> (
----      if any(M,isMonomial)
----         then error "this parameterization does not correspond to a toric ideal." 
----         else (
----              Mexp := apply(M, exponents);
----              transpose matrix apply(Mexp, flatten)))
----
---- isMonomial = method()
---- isMonomial RingElement := Boolean => (m) -> (
----      termList := terms m;
----      if #termList == 1 then true else false)

---- isMonomial works well as long as m is actually a polynomial or monomial and not 
---- an element of ZZ, QQ, RR, etc.

---- NOTE ALL basic graph functionality has been moved to Graphs.m2
---- Should removeNodes also be moved?

-------------------------
-- Digraph can now have any labels for the nodes, not just integers.
-- However, all the code in this package requires integer lables.  For
-- now, we just conver the labels with an eye towards fixing all the
-- code. 
-------------------------


convertToIntegers := (G) -> (
     n := #G;
     h := new MutableHashTable;
     scan(n, i -> h#(i+1) = (values G)#i);
     mid := new MutableHashTable;
     vertices := keys G;
     scan(n, i -> mid#(vertices#i) = (keys h)#i);
     scan(n, i -> h#(i+1) = set apply(toList h#(i+1), j -> mid#j));
     new Digraph from h
     )

-----------------------------------------------------------
-- Statement calculus ----  Local and Global Statements ---
-----------------------------------------------------------
-- A dependency is a list {A,B,C}x
--  where A,B,C are (disjoint) subsets of positive integers.
--  The meaning is: A is independent of B given C.
-- A dependency list is a list of dependencies

-- No serious attempt is made to remove redundant dependencies.
-- However, we have several very simple routines to remove
-- the most obvious redundant elements
-- If S and T represent exactly the same dependency, return true.


---- M2 does seem to remove dependencies reasonably well in removeRedundants, but 
---- it is definitely not finding all, only "obvious" ones in that function --- below 
---- the comment suggests "more serious removal of redundancies."
 
---- This is the section where the local and global statements are done. 

equivStmts = (S,T) -> S#2 === T#2 and set{S#0,S#1} === set{T#0,T#1}

-- More serious removal of redundancies.  This was taken from MES's indeps.m2
setit = (d) -> {set{d#0,d#1},d#2}

under = (d) -> (
     d01 := toList d_0;
     d0 := toList d01_0;
     d1 := toList d01_1;
     d2 := toList d_1;
     e0 := subsets d0;
     e1 := subsets d1;
     z1 := flatten apply(e0, x -> apply(e1, y -> (
		    {set{d01_0 - set x, d01_1 - set y}, set x + set y + d_1})));
     z2 := flatten apply(e0, x -> apply(e1, y -> (
		    {set{d01_0 - set x, d01_1 - set y}, d_1})));
     z = join(z1,z2);
     z = select(z, z0 -> not member(set{}, z0_0));
     set z
     )

-- input: ds
-- first make list where each element is {-a*b, set{A,B}, set C}
-- sort the list
-- remove the first element
sortdeps = Ds -> (
     i := 0;
     ds := apply(Ds, d -> (x := toList d#0; i=i+1; { - #x#0 * #x#1, i, d#0, d#1}));
     ds = sort ds;
     apply(ds, d -> {d#2, d#3})
     )

normalizeStmt = (D) -> (
     -- D has the form: {set{set{A},set{B}},set{C}}
     -- output is {A,B,C}, where A,B,C are sorted in increasing order
     --  and A#0 < B#0
     D0 := sort apply(toList(D#0), x -> sort toList x);
     D1 := toList(D#1);
     {D0#0, D0#1, D1}
     )
minimize = (Ds) -> (
     -- each element of Ds should be a list {A,B,C}
     answer := {};
     -- step 1: first make the first two elements of each set a set
     Ds = Ds/setit;
     while #Ds > 0 do (
	  Ds = sortdeps Ds;
	  f := Ds_0;
	  funder := under f;
	  answer = append(answer, f);
	  Ds = set Ds - funder;
	  Ds = toList Ds;
	  );
     apply(answer, normalizeStmt))

removeRedundants = (Ds) -> (
     -- Ds is a list of triples of sets {A,B,C}
     -- test1: returns true if D1 can be removed
     -- Return a sublist of Ds which removes any 
     --  that test1 declares not necessary.
     test1 := (D1,D2) -> (D1_2 === D2_2 and 
                          ((isSubset(D1_0, D2_0) and isSubset(D1_1, D2_1))
	               or (isSubset(D1_1, D2_0) and isSubset(D1_0, D2_1))));
     -- first remove non-unique elements, if any
     Ds = apply(Ds, d -> {set{d#0,d#1}, d#2});
     Ds = unique Ds;
     Ds = apply(Ds, d -> append(toList(d#0), d#1));
     c := toList select(0..#Ds-1, i -> (
	       a := Ds_i;
	       D0 := drop(Ds,{i,i});
	       all(D0, b -> not test1(a,b))));
     minimize(Ds_c))

--------------------------
-- Bayes ball algorithm --
--------------------------
bayesBall = (A,C,G) -> (
     -- A is a set in 1..n (n = #G)
     -- C is a set in 1..n (the "blocking set")
     -- G is a DAG
     -- Returns the subset B of 1..n which is
     --   independent of A given C.
     -- The algorithm is the Bayes Ball algorithm,
     -- as implemented by Luis Garcia, after
     -- the paper of Ross Schlacter
     n := #G;
     zeros := toList((n+1):false);
     visited := new MutableList from zeros;
     blocked := new MutableList from zeros;
     up := new MutableList from zeros;
     down := new MutableList from zeros;
     top := new MutableList from zeros;
     bottom := new MutableList from zeros;
     vqueue := sort toList A;
     -- Now initialize vqueue, set blocked
     scan(vqueue, a -> up#a = true);
     scan(toList C, c -> blocked#c = true);
     local pa;
     local ch;
     while #vqueue > 0 do (
	  v := vqueue#-1;
	  vqueue = drop(vqueue,-1);
	  visited#v = true;
	  if not blocked#v and up#v
	  then (
	       if not top#v then (
		    top#v = true;
		    pa = toList parents(G,v);
		    scan(pa, i -> up#i = true);
		    vqueue = join(vqueue,pa);
		    );
	       if not bottom#v then (
		    bottom#v = true;
		    ch = toList children(G,v);
		    scan(ch, i -> down#i = true);
		    vqueue = join(vqueue,ch);
		    );
	       );
	  if down#v
	  then (
	       if blocked#v and not top#v then (
		    top#v = true;
		    pa = toList parents(G,v);
		    scan(pa, i -> up#i = true);
		    vqueue = join(vqueue,pa);
		    );
	       if not blocked#v and not bottom#v then (
		    bottom#v = true;
		    ch = toList children(G,v);
		    scan(ch, i -> down#i = true);
		    vqueue = join(vqueue,ch);
		    );
	       );
	  ); -- while loop
     set toList select(1..n, i -> not blocked#i and not bottom#i)
     )

--------------------------
-- Markov relationships --
--------------------------
pairMarkovStmts = method()
pairMarkovStmts Digraph := (G) -> (
     -- given a graph G, returns a list of triples {A,B,C}
     -- where A,B,C are disjoint sets, and for every vertex v
     -- and non-descendent w of v,
     -- {v, w, nondescendents(G,v) - w}
     G = convertToIntegers(G);
     removeRedundants flatten apply(toList(1..#G), v -> (
	       ND := nondescendents(G,v);
	       W := ND - parents(G,v);
	       apply(toList W, w -> {set {v}, set{w}, ND - set{w}}))))

localMarkovStmts = method()			 
localMarkovStmts Digraph := (G) -> (
     -- Given a graph G, return a list of triples {A,B,C}
     -- of the form {v, nondescendents - parents, parents}
     G = convertToIntegers(G);
     result := {};
     scan(1..#G, v -> (
	       ND := nondescendents(G,v);
	       P := parents(G,v);
	       if #(ND - P) > 0 then
	         result = append(result,{set{v}, ND - P, P})));
     removeRedundants result)

///
restart 
loadPackage"GraphicalModels"
G = digraph({{a,{b,c}},{b,{c,d}},{c,{}},{d,{}}})
convertToIntegers(G)
 ///   


 
     ---- do a loop applying to the values first if g#blah is a member
     ---- of the set that is the value then convert to the appropriate
     ---- number. Not totally clear to me how to do this, or do we fix
     ---- bayes - ball.  Hmmm...


globalMarkovStmts = method()
globalMarkovStmts Digraph := (G) -> (
     -- Given a graph G, return a complete list of triples {A,B,C}
     -- so that A and B are d-separated by C (in the graph G).
     -- If G is large, this should maybe be rewritten so that
     -- one huge list of subsets is not made all at once
     G = convertToIntegers;
     n := #G;
     vertices := toList(1..n);
--     vertices := keys G;
     result := {};
     AX := subsets vertices;
     AX = drop(AX,1); -- drop the empty set
     AX = drop(AX,-1); -- drop the entire set
     scan(AX, A -> (
	       A = set A;
	       Acomplement := toList(set vertices - A);
	       CX := subsets Acomplement;
	       CX = drop(CX,-1); -- we don't want C to be the entire complement
	       scan(CX, C -> (
			 C = set C;
			 B := bayesBall(A,C,G);
			 if #B > 0 then (
			      B1 := {A,B,C};
			      if all(result, B2 -> not equivStmts(B1,B2))
			      then 
			          result = append(result, {A,B,C});
	       )))));
     removeRedundants result
     )
--- The function above gives output as they describe it,  the first
--- set is independent of the second set, given the third set.  

-------------------
-- Markov rings ---
-------------------
markovRingList = new MutableHashTable;
markovRing = d -> (
     -- d should be a sequence of integers di >= 1
     if any(d, di -> not instance(di,ZZ) or di <= 0)
     then error "useMarkovRing expected positive integers";
     p = value "symbol p";
     if not markovRingList#?d then (
     	  start := (#d):1;
     	  markovRingList#d = QQ[p_start .. p_d];
	  markovRingList#d.markov = d;
	  );
     markovRingList#d
     )

  --------------
  -- marginMap
  -- Return the ring map F : R --> R such that
  --   F p_(u1,u2,..., +, ,un) = p_(u1,u2,..., 1, ,un)
  -- and
  --   F p_(u1,u2,..., j, ,un) = p_(u1,u2,..., j, ,un), for j >= 2.
  --------------

marginMap = method()
marginMap(ZZ,Ring) := (v,R) -> (
     -- R should be a Markov ring
     v = v-1;
     d := R.markov;
     use R;
     F := toList apply(((#d):1) .. d, i -> (
	       if i#v > 1 then p_i
	       else (
		    i0 := drop(i,1);
		    p_i - sum(apply(toList(2..d#v), j -> (
			      newi := join(take(i,v), {j}, take(i,v-#d+1));
			      --print p_newi;
			      p_newi))))));
     map(R,R,F))

hideMap = method()
hideMap(ZZ,Ring) := (v,A) -> (
     -- creates a ring map inclusion F : S --> A.
     v = v-1;
     R := ring presentation A;
     d := R.markov;
     e := drop(d, {v,v});
     S := markovRing e;
     dv := d#v;
     use A;
     F := toList apply(((#e):1) .. e, i -> (
	       sum(apply(toList(1..dv), j -> (
			      newi := join(take(i,v), {j}, take(i,v-#d+1));
			      --print p_newi;
			      p_newi)))));
     map(A,S,F))



-------------------------------------------------------
-- Constructing the ideal of a independence relation --
-------------------------------------------------------
cartesian := (L) -> (
     if #L == 1 then 
	return toList apply (L#0, e -> 1:e);
     L0 := L#0;
     Lrest := drop (L,1);
     C := cartesian Lrest;
     flatten apply (L0, s -> apply (C, c -> prepend (s,c))))

possibleValues := (d,A) ->
     cartesian (toList apply(1..#d, i -> 
	       if member(i,A) 
	       then toList(1..d#(i-1)) 
	       else {0}))

prob = (d,s) -> (
     L := cartesian toList apply (#d, i -> 
	   if s#i === 0 
	   then toList(1..d#i) 
	   else {s#i});
     sum apply (L, v -> p_v))

markovMatrices = method()
markovMatrices(Ring,List) := (R, Stmts) -> (
     -- R should be a Markov ring, and S is a list of
     -- independence statements
     d := R.markov;
     flatten apply(Stmts, stmt -> (
     	       Avals := possibleValues(d,stmt#0);
     	       Bvals := possibleValues(d,stmt#1);
     	       Cvals := possibleValues(d,stmt#2);
     	       apply(Cvals, c -> (
                  matrix apply(Avals, 
		       a -> apply(Bvals, b -> (
				 e := toSequence(toList a + toList b + toList c);
		      		 prob(d,e))))))))
     )

markovIdeal = method()
markovIdeal(Ring,List) := (R,Stmts) -> (
     M := markovMatrices(R,Stmts);
     sum apply(M, m -> minors(2,m))
     )

gaussRing = method(Options=>{CoefficientRing=>QQ, Variable=>symbol s})
gaussRing ZZ := opts -> (n) -> (
     x := opts.Variable;
     kk := opts.CoefficientRing;
     v := flatten apply(1..n, i -> apply(i..n, j -> x_(i,j)));
     R := kk[v, MonomialSize=>16];
     R#gaussRing = n;
     R
     )

gaussMinors = method()
gaussMinors(Matrix,List) := (M,D) -> (
     -- M should be an n by n symmetric matrix, D mentions variables 1..n (at most)
     rows := join(D#0, D#2);
     rows = rows/(i -> i-1);
     cols := join(D#1, D#2);
     cols = cols/(i -> i-1);
     M1 = submatrix(M,rows,cols);
     minors(#D#2 + 1, M1)
     )

gaussIdeal = method()
gaussIdeal(Ring, List) := (R,Stmts) -> (
     -- for each statement, we take a set of minors
     if not R#?gaussRing then error "expected a ring created with gaussRing";
     M = genericSymmetricMatrix(R, R#gaussRing);
     sum apply(Stmts, D -> gaussMinors(M,D))     
     )
gaussIdeal(Ring,Digraph) := (R,G) -> gaussIdeal(R,globalMarkovStmts G)

gaussTrekIdeal = method()
gaussTrekIdeal(Ring, Digraph) := (R,G) -> (
     G = convertToIntegers(G);
     n := max keys G;
     P := toList apply(1..n, i -> toList parents(G,i));
     nv := max(P/(p -> #p));
     t := local t;
     S := (coefficientRing R)[generators R, t_1 .. t_nv];
     newvars := toList apply(1..nv, i -> t_i);
     I := trim ideal(0_S);
     sp := (i,j) -> if i > j then s_(j,i) else s_(i,j);
     for i from 1 to n-1 do (
	  J := ideal apply(1..i, j -> s_(j,i+1) 
	              - sum apply(#P#i, k -> S_(k + numgens R) * sp(j,P#i#k)));
	  I = eliminate(newvars, I + J);
	  );
     substitute(I,R)
     )

----------------------
-- Parameterization --
----------------------

---- We need this for both directed and undirected graphs. 


--------------------
-- Documentation  --
--------------------

beginDocumentation()

doc ///
  Key
    GraphicalModels
  Headline
    GraphicalModels ideals, arising from Bayesian networks in statistics
  Description
    Text
      This package is used to construct ideals corresponding to discrete graphical models,
      as described in several places, including the paper: Garcia, Stillman and Sturmfels,
      "The algebraic geometry of Bayesian networks", J. Symbolic Comput., 39(3-4):331–355, 2005.
  
      The paper also constructs Gaussian ideals, as described in the paper by Seth Sullivant:
      "Algebraic geometry of Gaussian Bayesian networks", Adv. in Appl. Math. 40 (2008), no. 4, 482--513.
      
      Here is a typical use of this package.  We create the ideal in 16 variables whose zero set 
      represents the probability distributions on four binary random variables which satisfy the
      conditional independence statements coming from the "diamond" graph 4 --> 2,3 --> 1.
    Example
      R = markovRing(2,2,2,2)
      G = makeGraph{{},{1},{1},{2,3}}
      S = globalMarkovStmts G
      I = markovIdeal(R,S)
    Text
      Sometime an ideal can be simplified by changing variables.  Very often, by using @TO marginMap@, 
      such ideals can be transformed to binomial ideals.  This is the case here.
    Example
      F = marginMap(1,R)
      J = F I;
      netList pack(2,J_*)
    Text
      This ideal has 5 primary components.  The first is the one that has statistical significance.
      The significance of the other components is still poorly understood.
    Example
      time netList primaryDecomposition J
  Caveat
    The parts of the package involving graphs might eventually be changed to use a package dealing
    specifically with graphs.  This might change the interface to this package.  
///

document { 
     Key => {gaussRing, (gaussRing,ZZ)},
     Headline => "ring of gaussian correlations on n random variables",
     Usage => "gaussRing n",
     Inputs => { 
	  "n" => ZZ => "the number of random variables",
	  CoefficientRing => "a coefficient field or ring",
	  Variable => "a symbol, the variables in the ring will be s_(1,1),..."
	   },
     Outputs => {
	  Ring => "a ring with indeterminates s_(i,j), 1 <= i <= j <= n"
	  },
     "The routines ", TO "gaussMinors", ", ", TO "gaussIdeal", ", ", TO "gaussTrekIdeal", 
     " all require that the ring
     be created by this function.",
     PARA{},
     EXAMPLE lines ///
     	  R = gaussRing 5;
	  gens R
	  genericSymmetricMatrix(R,5)
          ///,
     SeeAlso => {"gaussMinors", "gaussIdeal", "gaussTrekIdeal"}
     }

document { 
     Key => {gaussIdeal, (gaussIdeal,Ring,Digraph), (gaussIdeal,Ring,List)},
     Headline => "correlation ideal of a Bayesian network of joint Gaussian variables",
     Usage => "gaussIdeal(R,G)",
     Inputs => { 
	  "R" => Ring => {"created with ", TO  "gaussRing", ""},
	  "G" => {ofClass Digraph, " or ", ofClass List}
	   },
     Outputs => {
	  "the ideal in R of the relations in the correlations of the random variables implied by the
	  independence statements of the graph G or the list of independence statements G"
	  },
     "These ideals were first written down by Seth Sullivant, in \"Algebraic geometry of Gaussian Bayesian networks\". 
     The routines in this package involving Gaussian variables are all based on that paper.",
     EXAMPLE lines ///
          R = gaussRing 5;
	  G = makeGraph {{2},{3},{4,5},{5},{}}
	  (globalMarkovStmts G)/print;
	  J = gaussIdeal(R,G)
          ///,
     PARA{},
     "A list of independence statments (as for example returned by globalMarkovStmts)
     can be provided instead of a graph.",
     PARA{},
     "The ideal corresponding to a conditional independence statement {A,B,C} (where A,B,C,
     are disjoint lists of integers in the range 1..n (n is the number of random variables)
     is the #C+1 x #C+1 minors of the submatrix of the generic symmetric matrix M = (s_(i,j)), whose
     rows are in A union C, and whose columns are in B union C.  In general, this does not need to
     be a prime ideal.",
     EXAMPLE lines ///
          I = gaussIdeal(R,{{{1,2},{4,5},{3}}, {{1},{2},{3,4,5}}})
	  codim I
          ///,
     SeeAlso => {"makeGraph", "globalMarkovStmts", "localMarkovStmts", "gaussRing", "gaussMinors", "gaussTrekIdeal"}
     }

doc ///
  Key
    markovRing
  Headline
    ring of probability distributions on several discrete random variables
  Usage
    markovRing(d1,d2,...,dr)
  Inputs
    di:ZZ
      Each d_i should be a positive integer
  Outputs
    R:Ring
      A polynomial ring with d1*d2*...*dr variables $p_{(i1,...,ir)}$,
      with each i_j satisfying 1 <= i_j <= d_j.
  Consequences
    Information about this sequence of integers is placed into the ring, and is used 
    by other functions in this package.  Also, at most one ring for each such sequence
    is created: the results are cached.
  Description
   Example
     R = markovRing(2,3,4,5);
     numgens R
     R_0, R_1, R_119
     coefficientRing R
  Caveat
    Currently, the user has no choice about the names of the variables.  
    Also, the base field is set to be QQ, without option of changing it.
    These will hopefully change in a later version.  
  SeeAlso
///


end
doc ///
  Key
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///


doc ///
  Key
  Headline

  Usage

  Inputs

  Outputs

  Consequences

  Description
   Text
   Text
   Example
   Text
   Example
  Caveat
  SeeAlso
///

end
restart
loadPackage "Markov"
installPackage "Markov"
G = makeGraph{{},{1},{1},{2,3},{2,3}}
S = globalMarkovStmts G

R = markovRing(2,2,2,2,2)
markovIdeal(R,S)

R = gaussRing(5)

M = genericSymmetricMatrix(R,5)
describe R
gaussMinors(M,S_0)
J = trim gaussIdeal(R,S)
J1 = ideal drop(flatten entries gens J,1)
res J1
support J1

globalMarkovStmts G
minimize oo

G = makeGraph{{2,3},{4},{4},{}}
G1 = makeGraph{{},{1},{1},{2,3}}
globalMarkovStmts G
globalMarkovStmts G1

G4 = {{},{1},{1},{2,3}}

restart
loadPackage "Markov"
G4 = makeGraph{{2,3},{4},{4},{}}
R = gaussRing 4
I = gaussTrekIdeal(R,G4)
J = gaussIdeal(R,G4)
I == J

G4 = makeGraph{{2,3},{4},{4,5},{},{}}

G = makeGraph{{3},{3,4},{4},{}}
R = gaussRing 4
I = gaussTrekIdeal(R,G)
J = gaussIdeal(R,G)
I == J

load "/Users/mike/local/src/M2-mike/markov/dags5.m2"
D5s
D5s = apply(D5s, g -> (
	  G := reverse g;
	  G = apply(G, s -> sort apply(s, si -> 6-si));
	  G))
R = gaussRing 5
apply(D5s, g -> (
	  G := makeGraph g;
	  I := gaussTrekIdeal(R,G);
	  J := gaussIdeal(R,G);
	  if I != J then << "NOT EQUAL on " << g << endl;
	  I != J))

Gs = select(D5s, g -> (
	  G := makeGraph g;
	  I := gaussTrekIdeal(R,G);
	  J := gaussIdeal(R,G);
	  if I != J then << "NOT EQUAL on " << g << endl;
	  I != J))
Gs/print;
Gs = {
{{4}, {4}, {4, 5}, {5}, {}},
{{3, 5}, {3}, {4}, {5}, {}},
{{2, 4}, {4}, {4, 5}, {5}, {}},
{{2, 4}, {3, 5}, {4}, {5}, {}},
{{3, 5}, {3, 4}, {4}, {5}, {}},
{{2, 3, 5}, {4}, {4}, {5}, {}},
{{2, 4}, {3, 5}, {4, 5}, {5}, {}},
{{2, 3, 5}, {4}, {4, 5}, {5}, {}},
{{2, 4, 5}, {3, 5}, {4}, {5}, {}}
}

Gs/(g -> globalMarkovStmts makeGraph g)
scan(oo, s -> (s/print; print "-----------"));
G = makeGraph {{4}, {4}, {4, 5}, {5}, {}}
G = makeGraph {{3, 5}, {3}, {4}, {5}, {}}
G = makeGraph {{2, 4}, {4}, {4, 5}, {5}, {}}
G = makeGraph {{2, 4}, {3, 5}, {4}, {5}, {}}

G = makeGraph {{3, 5}, {3, 4}, {4}, {5}, {}}
G = makeGraph {{2, 3, 5}, {4}, {4}, {5}, {}}

G = makeGraph {{2, 4}, {3, 5}, {4, 5}, {5}, {}}
G = makeGraph {{2, 3, 5}, {4}, {4, 5}, {5}, {}}
G = makeGraph {{2, 4, 5}, {3, 5}, {4}, {5}, {}}

(globalMarkovStmts G)/print;
J = gaussIdeal(R,G)
I = gaussTrekIdeal(R,G)
J : I
res ideal select(flatten entries gens trim J, f -> first degree f > 1)
betti oo

i = 0
G = makeGraph D5s#i
I = gaussTrekIdeal(R,G)
J = gaussIdeal(R,G)
I == J
	  
removeNodes(G4,4)
G3 = drop(G4,-1)
G2 = drop(G3,-1)
debug Markov
G4 = makeGraph G4
parents(G4, 1)
parents(G4, 2)
parents(G4, 3)
parents(G4, 4)

-- We need a method to create all of the dags of size 6,7,8 (maybe not 8?)
- By hand let's do 6:
X = select(partitions 13, p -> #p <= 5)
X = select(X, p ->  p#0 <= 5)
X = select(X, p ->  #p <= 1 or p#1 <= 4)
X = select(X, p ->  #p <= 2 or p#2 <= 3)
X = select(X, p ->  #p <= 3 or p#3 <= 2)
X = select(X, p ->  #p <= 4 or p#4 <= 1)

X = select(partitions 11, p -> #p <= 6);
X = select(X, p ->  p#0 <= 6);
X = select(X, p ->  #p <= 1 or p#1 <= 5);
X = select(X, p ->  #p <= 2 or p#2 <= 4);
X = select(X, p ->  #p <= 3 or p#3 <= 3);
X = select(X, p ->  #p <= 4 or p#4 <= 2);
X = select(X, p ->  #p <= 5 or p#5 <= 1)

-- n=7 examples
restart
loadPackage "Markov"
load "/Users/mike/local/src/M2-mike/markov/dags5.m2"
F = lines get "dags7-part";
R = gaussRing 7


scan(F, g -> (
	  g = value g;
	  G := makeGraph g;
	  I := gaussTrekIdeal(R,G);
	  J := gaussIdeal(R,G);
	  << g;
	  if I != J then << " NOT EQUAL" << endl else << " equal" << endl;
	  ))

scan(F, g -> (
	  g = value g;
	  G := makeGraph g;
	  --I := gaussTrekIdeal(R,G);
	  J := trim gaussIdeal(R,G);
	  linears = ideal select(flatten entries gens J, f -> first degree f == 1);
	  J = trim ideal(gens J % linears);
	  << g << codim J << ", " << betti res J << endl;
	  ))

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=Markov pre-install"
-- End:
