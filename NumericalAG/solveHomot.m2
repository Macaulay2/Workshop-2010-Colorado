restart

needsPackage "NumericalAlgebraicGeometry"
needsPackage "NumericalSchubertCalculus"

--------------------------------------
--- solveHomotopic will be a function
--- to find solution from a specific instance 
--- of a Schubert problem using homotopy 
--- continuation starting from solving
--- another instance (hopefully easier) of
--- the Schubert problem, but with respect 
--- to a different flag
--------------------------------------

solveHomotopic = method(TypicalValue=>List)
solveHomotopic(Sequence, Sequence, List, List) := (kn,cond,G,F) ->(
   -- k and n are integers defining the Grassmannian G(k,n)
   (k,n) := kn;
   -- l and m are partitions of n
   (l,m) := cond;
   -- G is the start flag and F the target flag
   
   Sols:=solveSimpleSchubert(kn,l,m,G);
   E := skewSchubertVariety(kn,l,m);
   Start:=apply(G, g->det( matrix E || sub(g, ring E),Strategy=>Cofactor));
   Target:=apply(F,f->det( matrix E || sub(f, ring E),Strategy=>Cofactor));
	 track(Start,Target,Sols,gamma=>exp(2*pi*ii*random RR)) / first
)

findGaloisElement = method()
findGaloisElement(List, List, List) :=(prblm, flgs, solns) ->(
	-- prblm is a List that contains
	-- partitions l and m, and integers k,n 
	-- that define the 
	-- simple Schubert problem in Gr(k,n)
	{l,m,k,n}:=prblm;
	----- make sure both partitions are of size k  ----
	 x:={};
  if #l < k then x = for i to k-#l-1 list 0;
  l = l | x; -- makes sure l have size k
  if #m < k then x = for i to k-#m-1 list 0;
  m = m | x; -- makes sure m have size k
  ---------------------------------------------------
	--d := k*(n-k)-sum(l)-sum(m);
	-- create a random flag to start a loop
	-- We will work only from a short loop
	-- so we need only the first two rows
	-- of a random flag
  F := matrix apply(2, i->apply(n,j->random CC));
	swaps := {0,1,0,1};
	tmpMtrx := mutableMatrix flgs#d || F;
	tempSlns := solns;
	apply(swaps, j->(
	  M1 := submatrix'(tmpMtrx, {n-k, n-k+1});
		rowSwap(tmpMtrx,i, n-k+i);
		M2 := submatrix'(tmpMtrx, {n-k,n-k+1});
		tempSlns = solveHomotopic((k,n), (l,m), M1, M2);
	));
	position(solns, tempSlns, (i,j)-> i == j)
)

--- TEST ---
(k,n) = (3,7);
l = {2,1};
m = {1,1};
----  Generate random flags G----
d = k*(n-k)-sum(l)-sum(m);
G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
---------------------------------
S = solveSimpleSchubert((k,n),l,m,G);

findGaloisElement({l,m,k,n}, G, S)