needsPackage "NumericalSchubertCalculus"

isGaloisFullSymmetric = method()
isGaloisFullSymmetric(Sequence, List, List, ZZ) := (prblm, flgs, solns, mx) ->(
	-- mx is the maximal  number of loops we want to run
 	(l,m,k,n) := prblm;
	permuts := {toList(0..#solns-1)};
	cntr:= 0;
	for i from 1 to mx when (isFullSymmetric(permuts)===false) do (
	     permuts = permuts | {findGaloisElement(prblm,flgs,solns)};
	     cntr = i;
	);
   	if cntr < mx then(return true;)else(return (isFullSymmetric(permuts), drop(permuts,1)););
)

end

restart
needsPackage "NumericalSchubertCalculus"

p = {toList(0..4)};
p = permutations toList(0..3)
isFullSymmetric(p)


load "solveHomot.m2"


restart
--load "solveHomot.m2"
needsPackage "NumericalSchubertCalculus"
--- TEST GAP ---
perms = permutations 4;
isFullSymmetric( perms)
isFullSymmetric({perms#2})

--- TEST ---
(k,n) = (3,7);
l = {2,1};
m = {1,1};
----  Generate random flags G----
d = k*(n-k)-sum(l)-sum(m);
G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
---------------------------------
S = solveSimpleSchubert((k,n),l,m,G);

--- Test symmetric Group
isGaloisFullSymmetric((l,m,k,n),G,S,1)
isGaloisFullSymmetric((l,m,k,n),G,S,5)

l={1,1}
m={1}
(k,n)=(4,8);
d = k*(n-k)-sum(l)-sum(m);
G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
---------------------------------
S = solveSimpleSchubert((k,n),l,m,G);
#S
isGaloisFullSymmetric((l,m,k,n),G,S,3)


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
