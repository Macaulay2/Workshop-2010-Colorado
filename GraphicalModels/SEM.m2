newPackage("SEM",
     Authors => {
	  {Name => "Luis Garcia"},
	  {Name => "Alexander Diaz"}
	  },
     DebuggingMode => false,
     Headline => "Gaussian Library Translation",
     Version => "1"
     )



export {msize, shift, nonzerosize, pList, lList, directedEdges, bigraph, bidirectedEdges, identify, trekSeparation}

needsPackage "Graphs"

Bigraph = new Type of Graph
-- labeled different to tell the difference between undirected and bidirected edges

bigraph = method()
bigraph Graph := g -> (
	new Bigraph from g
)

pList = method()
pList(ZZ, MixedGraph) := (n, g) -> (
	join(toList(apply(1..n, i->p_(i,i))),delete(null,flatten(apply(keys(bidirectedEdges(g)), x-> apply((bidirectedEdges(g))#x, y->if x<y then p_(x,y))))))	
)	

lList = method()
lList(ZZ, MixedGraph) := (n, g) -> (
    delete(null,flatten(apply(keys(directedEdges(g)), x-> apply((directedEdges(g))#x, y->l_(x,y) ))))
)	

directedEdges = method()
directedEdges(MixedGraph) := (g) -> (
	scanKeys(g, i-> if class g#i === Digraph then u=g#i);
	u
)

bidirectedEdges = method()
bidirectedEdges(MixedGraph) := (g) -> (
	scanKeys(g, i-> if class g#i === Bigraph then v=g#i);
	v
)
	
identify = method()
identify(MixedGraph) := (g) -> (
	u := directedEdges(g);
	v := bidirectedEdges(g);
	n := #u;
	--changed v to vertices
	vertices := join(pList(n,g),lList(n,g));
	m := #vertices;

	SLP := QQ[pList(n,g),lList(n,g),s_(1,1)..s_(n,n), MonomialOrder => Eliminate m];
	SM := map(SLP^n,n,(i,j)->s_(i+1,j+1));
	
	PM := mutableMatrix(SLP,n,n);
	scan(1..n,i->PM_(i-1,i-1)=p_(i,i));
	scan(keys(v),i->scan(v#i, j->   
	    if i < j then
	      PM_(i-1,j-1) = p_(i,j)
	    else 
	      PM_(i-1,j-1) = p_(j,i)
	));
	print(PM);

	LM := mutableMatrix(SLP,n,n);
    scan(keys(u),i->scan(u#i, j->
        LM_(i-1,j-1) = l_(i,j)
    ));
	print(LM);

	Linv = inverse(1-matrix(LM));
	LiPL = transpose(Linv)*matrix(PM)*Linv;
	MPmLiPL := SM-LiPL;
	print(MPmLiPL);
	J := ideal(flatten(for i from 0 to n-1 list for j from i to n-1 list MPmLiPL_(i,j)));
	print(J);
	
	for t in vertices do
	(
	  Jmt := eliminate(delete(t,vertices),J);
	  
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

trekSeparation = method()
trekSeparation(MixedGraph) := (g) ->(
	u = directedEdges(mg);
	v = bidirectedEdges(mg);
	n = #u;
)
	
	
	
	
	
	
