restart
debug needsPackage "NumericalSchubertCalculus" 

---- Simple Schubert Problem
(k,n) = (3,7)
l = {2,1,0}
m = {1,1,0}
----  Generate random flags G----
d = k*(n-k)-sum(l)-sum(m);
G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
---------------------------------
S = solveSimpleSchubert((k,n),l,m,G);

     
