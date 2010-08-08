restart

needs "pieriHom.m2":

--launchSimpleSchubert = method()
--launchSimpleSchubert(Sequence, List, List) := (kn,l,m)->(

   -- l and m are partitions of n
--   (k,n) := kn;
--   d := k*(n-k)-sum(l)-sum(m); -- d is the size of the system
   
--   G = apply(d, i->matrix apply(n-k,i->apply(n,j->random CC)));
   -- G is a family of n-k random numerical matrices
--   print G;
--   H = new MutableHashTable from {};
--   solveSimpleSchubert(kn,l,m)
--   )

--precookPieriHomotopy((3,7),{2,1,0},{1,1,0})
launchSimpleSchubert((2,4),{1,0},{1,0})
--launchSimpleSchubert((3,7),{2,1,0},{1,1,0})

