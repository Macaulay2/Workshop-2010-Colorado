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

trackSimpleSchubert = method(TypicalValue=>List)
trackSimpleSchubert(Sequence, Sequence, List, List) := (kn,cond,G,F) ->(
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
findGaloisElement(Sequence, List, List) :=(prblm, flgs, solns) ->(
     -- prblm is a List that contains
     -- partitions l and m, and integers k,n 
     -- that define the 
     -- simple Schubert problem in Gr(k,n)
     (l,m,k,n):=prblm;
     ----- make sure both partitions are of size k  ----
     x:={};
     if #l < k then x = for i to k-#l-1 list 0;
     l = l | x; -- makes sure l have size k
     if #m < k then x = for i to k-#m-1 list 0;
     m = m | x; -- makes sure m have size k
     ---------------------------------------------------
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
	       tempSlns = trackSimpleSchubert((k,n), (l,m), drop(flgs, -1) | {M1}, drop(flgs, -1) | {M2});
	       ));
     apply(solns, s->positions(tempSlns, j->areEqual(j,s))) / first
     )
end

restart
load "solveHomot.m2"
--- TEST ---
(k,n) = (3,7);
l = {2,1};
m = {1,1};
----  Generate random flags G----
d = k*(n-k)-sum(l)-sum(m);
G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
---------------------------------
S = solveSimpleSchubert((k,n),l,m,G);

findGaloisElement((l,m,k,n), G, S)

	F = matrix apply(2, i->apply(n,j->random CC));
   swaps = {0,1,0,1};
   tmpMtrx = mutableMatrix(G#(d-1) || F);
   tempSlns = S;
   apply(swaps, j->(
       M1 = submatrix'(matrix tmpMtrx, {n-k, n-k+1},);
       rowSwap(tmpMtrx, j, n-k+j);
       MN2 = submatrix'(matrix tmpMtrx, {n-k,n-k+1},);
       tempSlns = solveHomotopic((k,n), (l,m), drop(G, -1) | {M1}, drop(G, -1) | {MN2});
       ));
   apply(S, s->positions(tempSlns, j-> areEqual(j,s)))   

///
###############################################################################
# Launches GAP to see if "perms" generate a full symmetric group
isFullSymmetricViaGAP := proc(f::string,perms::list)
local g, p;
  g := ""||f||".gapjob";
  fopen(g,WRITE);
  fprintf( g, "u := Group(\n" );
  for p in perms do
   if lhs(p) = 'cycle' then
     fprintf( g, "(%q),\n", rhs(p)[] );
   elif lhs(p) = 'plist' then
     fprintf( g, "PermList(%a),\n", rhs(p) );
   else error "uknown type of permutation";
   fi;
  od;
  fprintf( g, "());\n");
  fprintf( g, "if NrMovedPoints(u)=%d and IsNaturalSymmetricGroup(u) then RemoveFile(\"%s\"); fi;\n", nSols, g);
  fprintf( g, "QUIT;\n");
  fclose(g);
  ssystem("gap "||g);
  #print(ssystem("c/gap4r4/bin/gap.bat"||g));
  return evalb(not FileTools[Exists](g));
end proc:
///