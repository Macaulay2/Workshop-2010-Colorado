newPackage(
        "NumericalSchubertCalculus",
        Version => "0.1", 
        Date => "October 29, 2009",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "a Macaulay2 package for using numerical methods in Schubert Calculus",
        DebuggingMode => true
        )

export {   
	 skewSchubertVariety,
 	 createRandomFlagsForSimpleSchubert,
	 solveSimpleSchubert,
	 trackSimpleSchubert,
	 findGaloisElement,
	 isFullSymmetric,
	 isGaloisFullSymmetric,
         Memoize
   }

-------------------------
-- Pieri Homotopy Code --
--------------------------
-- Authors: Anton Leykin
--          Abraham Martin del Campo
--
-- Date:  October 29, 2009
--
-- Last Update: August 11, 2010
-----------------------

needsPackage "NumericalAlgebraicGeometry"

solutionsHash := new MutableHashTable;

---------------------
--	verifyLength	--
--								--
-- makes sure a partition l
-- that is supposed to impose
-- conditions on Gr(k,n)
-- is in fact a partition 
-- of length k (add 0s if not)
--
verifyLength = method(TypicalValue => List)
verifyLength(VisibleList, ZZ) := (l,k) ->(
     x:=new List;
     if #l < k then x = for i to k-#l-1 list 0;
     l | x
)

---------------------------
--  skewSchubertVariety  --
-- Creates Matrix E_{m,l} --
---------------------------
skewSchubertVariety = method(TypicalValue=>Matrix)
skewSchubertVariety(Sequence,List,List) := (kn,l,m)->(
     -- k and n are the integers defining the Grassmanian G(k,n)
     -- l and m are partitions of n
     (k,n):=kn;
     l = verifyLength(l, k);
     m = verifyLength(m, k);
     d := (k*(n-k)-sum(l)-sum(m));
     R := CC[vars(53..d+52)]; -- ring where the variables for the matrix lie
     r := 0;
     matrix (
     	  for i from 1 to k list (
               for j from 1 to n list (
               	    if j==i+l_(k-i) then 1
		    else if j>i+l_(k-i) and j<=(n-k+i-m_(i-1)) then ( 
		     	          r=r+1; 
		     	          R_(r-1) 
		     	         )
            	    else 0
         	     ) 
      	       )
      	  )
     )

---------------------
-- Generate partitions for 
-- Children problems of a 
-- partition 'm' 
---------------------
generateChildren = method(TypicalValue=>List)
generateChildren(Sequence, List, List) := (kn, l, m) -> (
     (k,n):=kn;
     L := apply(#m, i->if n-k-l#(k-i-1)>=m#i+1 then take(m,i)|{m#i+1}|drop(m,i+1));
     select(L, a-> a=!=null and a==reverse sort a)
)

-------------------
-- find the position where you need
-- to add a solution of the children problem
-- to have a solution of the parent problem
------------------
positionVariableChildren = method(TypicalValue=>ZZ)
positionVariableChildren(Sequence,List,List,List):=(kn,l,m,v)->(
   -- kn is a sequence (k,n)
   -- l, m are partitions
   -- v is a children partition of m 
   (k,n) := kn;
   i := maxPosition(v-m);
   t := apply(i+1, j->plus(n-k-m_(j)-l_(k-j-1)));
   sum(t)
)


insertSolution = method(TypicalValue=>List)
insertSolution(List,List) := (v,s) ->(
   ---------------
   -- v is a children partition
   -- s is a solution of the children problem E(l,v)
   ------------------------
   i:=positionVariableChildren(kn,l,m,v);
   take(s,i)|{0}|drop(s,i)
)


-----------------------
-- precookPieri
--
-- creates a special matrix G_\mu
-- and attach it to E_{\mu\lambda}
----------------------- 
precookPieriHomotopy = method(TypicalValue=>List)
precookPieriHomotopy(Sequence,List,List) := (kn,l,m)->(
     -- k and n are the integers defining the Grassmanian G(k,n)
     -- l and m are partitions of n
     (k,n) := kn;
     l = verifyLength(l, k);
     m = verifyLength(m, k);
     E := skewSchubertVariety(kn,l,m);
     ------------
     -- d is the number of variables i.e. the codimension of the Schubert variety E_{l,m}
     ------------
     d := (k*(n-k)-sum(l)-sum(m));
     S := CC[vars(53..d+52)];
     T:= apply(#m, i->n-k+i-m#i);
     -- P is a list with the indeces where the special flag has ones
     P:=toList(set toList(0..n-1)-T);
     G:=mutableMatrix(S,n-k,n);
     apply(#P, j->G_(j,P#j)=1);
     F:=matrix E || sub(matrix G, ring E);
     return F;
)

--------------------------
-- Given the partitions l, and m for the Grassmannian Gr(k,n)
-- it creates a flags as random numeric matrices G_1,...,G_m
-- for solving the system defined by these random matrices
-- using Homotopy Continuation
--------------------------
createRandomFlagsForSimpleSchubert = method( )
createRandomFlagsForSimpleSchubert(Sequence, List, List) := (kn,l,m)->(
	 (k,n) := kn;
	 l = verifyLength(l, k);
	 m = verifyLength(m, k);
   d := k*(n-k)-sum(l)-sum(m);
   apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)))
   )

     
solveSimpleSchubert = method(TypicalValue=>List)
solveSimpleSchubert(Sequence,List,List,List) := (kn,l,m,G)->(
   -- l and m are partitions of n
   -- G is a flag
   (k,n) := kn;
   l = verifyLength(l, k);
   m = verifyLength(m, k);
   d := k*(n-k)-sum(l)-sum(m);
   E := skewSchubertVariety(kn,l,m);
   if solutionsHash#?{l,m,G} then(
   	 solutionsHash # {l,m,G}
   )
   else if d == 1 then (
      -- solve linear equation
      solutionsHash#{l,m,G} = solveEasy det (matrix E || sub(G#0, ring E), Strategy=>Cofactor)
   )
   else(
      -- generate the children problems
      L:=generateChildren(kn, l,m);
      
      -- once the children problems are solved
      -- store solutions in "start" 
      start := flatten(apply(L, p->(
         C := solveSimpleSchubert(kn,l,p,G);
         i := positionVariableChildren((k,n),l,m,p);
         apply(C,c->insert(i-1,0,c))
         )
      ));
      ---- Create the start system S  ----
      S := apply(take(G,d-1), g->det( matrix E || sub(g, ring E),Strategy=>Cofactor)) | {det(precookPieriHomotopy(kn,l,m), Strategy=>Cofactor)};
      ---- Create the target system T ----
      T := apply(take(G,d), g->det( matrix E || sub(g, ring E), Strategy=>Cofactor)); 
      newR := CC_53(monoid[gens ring first S]);
      S = S/(s->sub(s,newR));
      T = T/(t->sub(t,newR));
      ------------------------
      -- make sure your starting set of solutions are in fact solutions
      -- of the Starting system S
      ------------------------
      assert all(start, s->norm sub(matrix{S},matrix{s}) < 1e-3);
      solutionsHash#{l,m,G} = track(S,T,start,gamma=>exp(2*pi*ii*random RR)) / coordinates;
      ---------------------
      ---- make sure that you got solutions of the Target System --
      ---------------------
      assert all(solutionsHash#{l,m,G}, s->norm sub(matrix{T},matrix{s}) < 1e-3);
      solutionsHash#{l,m,G}
   )
)


-----------------------------
---- function written to solve
---- a simple linear equation
solveEasy = method(TypicalValue=>CC)
solveEasy(RingElement) := (p)->(
   R:=ring p;
   var:=support p;
   b:=part(0,p);
   a:=p_(var_(0));
   -- print(p,a,b);
   {{toCC sub((-b)/a, coefficientRing R)}}
)


--------------------------------------
--- trackSimpleSchubert
--------------------------------------
---
--- A function to find solution from a specific instance 
--- of a Schubert problem using homotopy 
--- continuation starting from solving
--- another instance (hopefully easier) of
--- the Schubert problem, but with respect 
--- to a different flag
--------------------------------------

trackSimpleSchubert = method(TypicalValue=>List, Options=>{Memoize => false, StartSolutions=>null})
trackSimpleSchubert(Sequence, Sequence, List, List) := o->(kn,cond,G,F) ->(
   -- G is the start flag and F the target flag
   -- k and n are integers defining the Grassmannian G(k,n)
   (k,n) := kn;
   -- l and m are partitions of n
   (l,m) := cond;
   Sols:= (if o.StartSolutions === null then solveSimpleSchubert(kn,l,m,G) else o.StartSolutions);
   E := skewSchubertVariety(kn,l,m);
   Start:=apply(G, g->det( matrix E || sub(g, ring E),Strategy=>Cofactor));
   Target:=apply(F,f->det( matrix E || sub(f, ring E),Strategy=>Cofactor));
   Ret:=track(Start,Target,Sols,gamma=>exp(2*pi*ii*random RR)) / coordinates;
   if o.Memoize then solutionsHash#{l,m,F} = Ret;  
   return Ret;
)

-------------------------------
---  findGaloisElement
-------------------------------
--- A function that computes
--- another instances of a
--- given Schubert problem to
--- create a short loop
--- and track the solutions
--- using homotopy continuation,
--- then extracts the created
--- permutation of the solutions

findGaloisElement = method(TypicalValue => List)
findGaloisElement(Sequence, List, List) :=(prblm, flgs, solns) ->(
    ---------------------------------
     -- prblm 
     -- is a List that contains partitions 
     -- l and m, and integers k,n 
     -- that define the simple 
     -- Schubert problem in Gr(k,n)
     (l,m,k,n):=prblm;
     l = verifyLength(l, k);
     m = verifyLength(m, k);
     d := k*(n-k)-sum(l)-sum(m);
     -- create a random flag to start a loop
     -- We will work only from a short loop
     -- so we need only the first two rows
     -- of a random flag
     F := matrix apply(2, i->apply(n,j->random CC));
     swaps := {0,1,0,1};
     tmpMtrx := mutableMatrix(flgs#(d-1) || F);
     tempSlns := solns;
     apply(swaps, j->(
	       M1 := submatrix'(matrix tmpMtrx, {n-k, n-k+1},);
	       rowSwap(tmpMtrx, j, n-k+j);
	       M2 := submatrix'(matrix tmpMtrx, {n-k,n-k+1},);
	       tempSlns = trackSimpleSchubert((k,n), (l,m), drop(flgs, -1) | {M1}, drop(flgs, -1) | {M2}, StartSolutions=>tempSlns);
	       ));
     apply(solns, s->positions(tempSlns, j->areEqual(j,s))) / first
)

------------------
-- isFullSymmetric
-- is a function that
-- takes a list of permutations
-- creates a file and run
-- GAP to test if the list
-- generates the full symmetric group
--
-- CAVIAT: it assumes that GAP runs
-- 	   when you type "gap" in a 
--	   terminal
------------------

getFileName = () -> (
	filename := temporaryFileName();
	while fileExists(filename) or fileExists(filename|".mat") or fileExists(filename|".lat") do filename = temporaryFileName();
	filename
	)

--GAPexe ="/Applications/gap4r4/bin/./gap.sh";	
GAPexe := "gap";

isFullSymmetric = method(TypicalValue => Nothing)
isFullSymmetric(List) := (perms)->(
	--
	-- perms is a list of permutations
	-- of [n] = {1,2,...,n}
	--
	F := getFileName();
	file := openOut(F|".gapjob");
	file << "u := Group(" << endl;
	scan(#perms, i->
		(
			p := perms#i;
			file << "PermList([" ;
			scan(p, j->( 
				file << j+1; 
				if j=!= last p then file << ", " ;
			));
			file <<"])";
			if i=!=#perms-1 then file << ", "<<endl; 
		)
	);
	file <<endl << ");"<<endl;

	n := max perms#0;
	file <<"if NrMovedPoints(u)="<< n+1 << " and IsNaturalSymmetricGroup(u) then RemoveFile(\""<< toString(file) <<"\"); fi;\n";
	file << "QUIT;\n";
	close file;
  	--------------
	--
	-- Running GAP
	--
	--------------
	run(GAPexe|" -q "|toString(file));
	if fileExists toString(file) then (
		removeFile toString(file); 
		return false;
	)else(
		return true;
	)
)

-------------------
--
--	isGaloisFullSymmetric
--
-------------------
-- function that find Galois
-- elements of a Schubert Problem
-- until it gets the full symmetric
-- group
--
-- CAVIAT: this assumes that we
-- know that Gal(Prblm) = symm_n
--
-------------------
isGaloisFullSymmetric = method()
isGaloisFullSymmetric(Sequence, List, List, ZZ) := (prblm, flgs, solns, mx) ->(
	-- mx is the maximal number of loops we want to run
 	(l,m,k,n) := prblm;
	permuts := new List;
	cntr:= 0;
	tempOut := false;
	for i from 1 to mx when (tempOut===false) do (
	     permuts = permuts | {findGaloisElement(prblm,flgs,solns)};
	     cntr = i;
	     tempOut = isFullSymmetric(permuts);
	);
	if tempOut then (
		(tempOut, cntr) 
	)else (
		(tempOut, permuts)
	)
)

-------------------
-- Documentation --
-------------------

beginDocumentation()

doc ///
   Key
      skewSchubertVariety
   Headline
      skew Schubert variety (or Richardson variety) from partitions $l$ and $m$
   Usage
      skewSchubertVariety(kn,l,m)
   Inputs
      kn:Sequence
         two integers denoting the Grassmannian Gr(k,n)
      l:List
      m:List
         partitions of n
   Outputs
      :Matrix
   Consequences
      Matrix with some indeterminate entries that parametrizes the skew Schubert variety 
   Description
      Text
         Creates the matrix $E_{l,m}$ that parametrizes the skew Schubert variety $Y_{l,m} = Y_l \cap Y_m$.
      Example
         -- for l = 2,1 and m = 1,1
       	 -- in Gr(3,7)
      	 skewSchubertVariety( (3,7),{2,1},{1,1} )
   SeeAlso
         solveSimpleSchubert
///;

doc ///
   Key
      createRandomFlagsForSimpleSchubert
   Headline
      Create a list of flags with random numbers to solve a simple Schubert problem
   Usage
      createRandomFlagsForSimpleSchubert(kn,l,m)
   Inputs
      kn:Sequence
         two integers denoting the Grassmannian Gr(k,n)
      l:List
      m:List
         partitions of n
   Outputs
      :List
         random fixed flags
   Description
      Text
         Creates a list of d matrices with random numbers, where $d = k*(n-k)-|m|-|l|$.
      Example
         -- for l = 2,1 and m = 1,1
      	 -- in Gr(3,7)
      	 createRandomFlagsForSimpleSchubert((3,7),{2,1,0},{1,1,0})
   SeeAlso
         solveSimpleSchubert
///;

doc ///
   Key
      solveSimpleSchubert
   Headline
      Uses Pieri Homotopy continuation to solve simple Schubert problems
   Usage
      solveSimpleSchubert(kn,l,m,G)
   Inputs
      kn:Sequence
         two integers denoting the Grassmannian Gr(k,n)
      l:List
      m:List
         partitions of n
      G:List
         of fixed Flags G_1,...,G_d
   Outputs
      :List
         solutions of the simple Schubert Problem defined by l and m with respect to the flags G_1,...,G_d
   Description
      Text
         Given partitions $l$ and $m$ in the Grassmannian $Gr(k,n)$, and a set of fixed flags $G_1,...,G_d$, where $d=k*(k-n) - |l| - |m|$. The function solves the system taking the first $d-1$ flags, and replacing the last one for a simpler one $G_m$. Then it uses homotopy continuation to track the solutions of this simpler system to solutions of the original system.         
    	 This function is used to solve Simple Schubert Problems, as described in the paper:          
    	 Leykin and Sottile, "Galois groups of Schubert problems via homotopy continuation", Mathematics of Computation, 78 (2009) 1749--1765.
      Example
         ---- Simple Schubert Problem
       	 k = 3
	 n = 7
       	 l = {2,1,0}
       	 m = {1,1,0}
       	 ----  Generate random flags G----
       	 d = k*(n-k)-sum(l)-sum(m);
       	 G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
       	 ---------------------------------
       	 solveSimpleSchubert((k,n),l,m,G)
   SeeAlso
         createRandomFlagsForSimpleSchubert 
         skewSchubertVariety
///;

doc ///
    Key
       trackSimpleSchubert
    Headline
       Uses Homotopy continuation to solve a Schubert problem
    Usage
       trackSimpleSchubert(kn,cond, G, F)
    Inputs
         kn:Sequence
            two integers (k,n) denoting the Grassmannian Gr(k,n)
         cond:Sequence
            of two partitions of n
         G:List
            of starting Flags G_1,..., G_d
         F:List
            of target Flags F_1,...,F_d
    Outputs
         :List
            solutions of the Schubert problem defined by l and m with respect to the flags F_1,...,F_d
    Description
       Text
          Given partitions $l$ and $m$ in the Grassmannian $Gr(k,n)$, and two sets of fixed flags $G_1,...,G_d$, and $F_1,...,F_d$; where $d=k*(k-n) - |l| - |m|$. The function tracks the solutions of the system defined by $G_1,...,G_d$ (if the solutions are not given, it computes them using {\tt solveSimpleSchubert}) to find solutions for the system defined by $F_1,...,F_d$. 
       Example
         ---- Simple Schubert Problem
   	 (k,n) = (3,7)
   	 l = {2,1,0}
   	 m = {1,1,0}
   	 ----  Generate random flags G and F----
   	 d = k*(n-k)-sum(l)-sum(m);
   	 G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
   	 F = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
   	 ---------------------------------
   	 trackSimpleSchubert((k,n),(l,m),G,F)
       
      Text
         If the solutions of the system defined by $G_1,...,G_d$ are given, they can be given in the function to avoid unnecessary computations
      Example
         ---- Simple Schubert Problem
   	 (k,n) = (3,7)
   	 l = {2,1,0}
   	 m = {1,1,0}
   	 ----  Generate random flags G and F----
   	 d = k*(n-k)-sum(l)-sum(m);
   	 G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
   	 F = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
   	 ---------------------------------
   	 Solns = solveSimpleSchubert((k,n),l,m,G);
         trackSimpleSchubert((k,n),(l,m),G,F, StartSolutions=>Solns)
   SeeAlso
         solveSimpleSchubert
         createRandomFlagsForSimpleSchubert
///;

doc ///
   Key
      findGaloisElement
   Headline
      computes a permutation from a loop of an instance of a simple Schubert problem.
   Usage
      findGaloisElement(pblm, flag, solns)
   Inputs
      pblm:Sequence
         a sequence (l,m,k,n) that contains two partitions l,m and two integers k,n that define the simple Schubert problem l,m in the Grassmannian Gr(k,n)
      flag:List
         a list of numerical matrices that define an instance of the simple Schubert Problem
      solns:List
         solutions of the specific instance
   Outputs
      :List
         a permutation that lie in the Galois group
   Description
      Text
         Given a simple Schubert problem $(l,m)$ in $Gr(k,n)$. Fix a 
	 set of flags $F_1,...,F_d$ and let $S$ be the set of solutions of
	 the intance of the Schubert problem given by the flags $\{F_i\}$.
	 We compute a loop in the problem space based on the solution $S$
	 by deforming one of the flags $F_i$ using Homotopy continuation. 
	 This  generates a loop in the problem space, which corresponds to 
	 a permutation in the Galois group.
      Example
         l={1,1}
	 m={2,1}
	 (k,n) = (3,7)
	 d = k*(n-k)-sum(l)-sum(m);
	 ---
	 --- Generate a random set of flags
	 --- to compute an instance of the problem	 
	 G = createRandomFlagsForSimpleSchubert((k,n),l,m)	 
	 ---------------------------------
	 ---  Solve the problem
	 S = solveSimpleSchubert((k,n),l,m,G);
	 --------------------------------
	 -- This is a problem with 77 solutions
	 #S
	 --
	 -- an element of the Galois group is:
	 --
	 findGaloisElement((l,m,k,n), G, S)
   SeeAlso
      isFullSymmetric
      isGaloisFullSymmetric 
      solveSimpleSchubert
      createRandomFlagsForSimpleSchubert
///;

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

