newPackage("SEM1",
     Authors => {
	  {Name => "Luis Garcia"},
	  {Name => "Alexander Diaz"}
	  },
     DebuggingMode => false,
     Headline => "Gaussian Library Translation",
     Version => "1"
     )

--loadPackage "Gausianlib"

--this is a comment
--the main data type will be a graph
--it will consist of two hash tables
--the first hash table will have each node => list of its children
--the second hash will be for bidirected edges and will have each node => list of its children
--example of a list: x = {1, 2, 3, 4}
--example of a hash table: g1 = new HashTable from {1 => {2}, 2 => {3,4}, 3 => {}, 4 => {}}

--example of the data structure "graph":
--g1 = new HashTable from {1 => {2}, 2 => {3,4}, 3 => {}, 4 => {}}
--g2 = new HashTable from {1 => {2}, 2 => {1}, 3 => {}, 4 => {}}
--graph = {g1, g2}


export {msize, shift, nonzerosize, pList, lList, identify}


--msize = method()
--msize(ZZ) := (n) -> (n*(n-1)/2);

--shift = method()
--shift(List) := (v) -> (
--	myv := new MutableList from v;
--	for i from 0 to (#v-1) do (myv#i = myv#i -1);
--	toList(myv))

--nonzerosize = method()
--nonzerosize(List) := (v) -> (
--	num:=0;
--	for i from 0 to (#v-1) do (
--		if(v#i != 0) then
--		(num = num + 1));
--	num)

--take this method out, eventually
--sList = method()
--sList(ZZ) := (n) -> (
--	toList(s_(1,1)..s_(n,n)))

pList = method()
pList(ZZ, HashTable) := (n, g) -> (
	join(toList(apply(1..n, i->p_(i,i))),delete(null,flatten(apply(keys(g#((keys(g))_1)), x-> apply(g#((keys(g))_1)#x, y->if x<y then p_(x,y) )))))	
)	

lList = method()
lList(ZZ, List) := (n, g) -> (
    delete(null,flatten(apply(keys(g#0), x-> apply(g#0#x, y->l_(x,y) ))))
)	

identify = method()
identify(MixedGraph) := (g) -> (
	n := #g#((keys(g))_0);
	v := join(pList(n,g),lList(n,g));
	print(v);
	m := #v;

	SLP := QQ[pList(n,g),lList(n,g),s_(1,1)..s_(n,n), MonomialOrder => Eliminate m];
	SM := map(SLP^n,n,(i,j)->s_(i+1,j+1));
	
	PM := mutableMatrix(SLP,n,n);
	scan(1..n,i->PM_(i-1,i-1)=p_(i,i));
	scan(keys(g#1),i->scan(g#1#i, j->   
	    if i < j then
	      PM_(i-1,j-1) = p_(i,j)
	    else 
	      PM_(i-1,j-1) = p_(j,i)
	));
	print(PM);

	LM := mutableMatrix(SLP,n,n);
    scan(keys(g#0),i->scan(g#0#i, j->
        LM_(i-1,j-1) = l_(i,j)
    ));
	print(LM);

	Linv = inverse(1-matrix(LM));
	LiPL = transpose(Linv)*matrix(PM)*Linv;
	MPmLiPL := SM-LiPL;
	print(MPmLiPL);
	J := ideal(flatten(for i from 0 to n-1 list for j from i to n-1 list MPmLiPL_(i,j)));
	print(J);
	
	for t in v do
	(
	  Jmt := eliminate(delete(t,v),J);
	  
	  -- the parameter we are checking identifiability with
	  print(t);
	  
	  -- whether the image of the parametrization is dense in the probability space
	  -- non-zero if it is dense, 0 if it is not dense
	  print(min(apply(Jmt_*, q->degree(t,q))));
	  
	  -- minimum number of points in the fiber over a point in the image
	  print(min(delete(0,apply(Jmt_*, q->degree(t,q)))));
	  
	  -- ideal of equations containing s_(i,j) and the parameter q
	  print(Jmt);
	);
	--
	
)

--trek_separation = method()
--trek_separation(MixedGraph) := (g) ->(
--	n = #g#((keys(g))_0);
--	h = g#((keys(g))_1);
	
--)
	
	
	
	
	
	
