newPackage("SEM",
     Authors => {
	  {Name => "Luis Garcia"},
	  {Name => "Alexander Diaz"}
	  },
     DebuggingMode => false,
     Headline => "Gaussian Library Translation",
     Version => "1"
     )



export {identify, 
	trekSeparation}

needsPackage "Graphs"

-- returns the position in list h of the key x
pos := (h, x) -> position(h, i->i===x)

-- returns the hash table M of hash tables storing the adjacency matrix of a digraph G,where M#a#b is true if a->b, and false otherwise.
adjacencyHashTable := (G) -> (
        G1 := graph G;
     	VV := vertices G;
     	hashTable apply(VV,i->{i,hashTable apply(VV,j->{j,#positions(toList G1#i,k->k===j)})}))

-- takes a list A, and a sublist B of A, and converts the membership sequence of 0's and 1's of elements of B in A to binary
setToBinary := (A,B) -> sum(toList apply(0..#A-1, i->2^i*(if (set B)#?(A#i) then 1 else 0)))

-- returns all subsets of B which contain A
subsetsBetween := (A,B) -> apply(subsets ((set B) - A), i->toList (i+set A))



identify = method()
-- Input: a MixedGraph
-- Output: a hash table H where for each parameter t, H#t is the ideal of relations involving t and the entries of the covariance matrix.
identify MixedGraph := (g) -> (
        G := graph collateVertices g;
	dd := graph G#Digraph;
	bb := graph G#Bigraph;
	vv := sort vertices g;
	n := #vv;
	
	--create list of variables corresponding to Bidirected edges
	pL := join(apply(vv, i->p_(i,i)),delete(null,flatten(apply(vv, x-> apply(toList bb#x, y->if pos(vv,x) < pos(vv,y) then p_(x,y))))));
     	--create list of variables corresponding to Directed edges
	lL := delete(null,flatten(apply(vv, x-> apply(toList dd#x, y->l_(x,y) ))));	 
        -- create ring with all the parameters p_(i,j),l_(i,j),s_(i,j) with intent of eliminating p's and l's
	m := #edges(G#Digraph)+#edges(G#Bigraph)+n;
	SLP := QQ[pL,lL,s_(1,1)..s_(n,n), MonomialOrder => Eliminate m];
	plvars = toList apply(0..m-1,i->(flatten entries vars SLP)#i);

        -- create symmetric covariance matrix \Sigma
	SM := map(SLP^n,n,(i,j)->if i<j then s_(i+1,j+1) else s_(j+1,i+1));
	-- create symmetric matrix \Phi for Bidirected edges
	PM := mutableMatrix(SLP,n,n);
	scan(vv,i->PM_(pos(vv,i),pos(vv,i))=p_(i,i));
	scan(vv,i->scan(toList bb#i, j->PM_(pos(vv,i),pos(vv,j))=if pos(vv,i)<pos(vv,j) then p_(i,j) else p_(j,i)));
        -- create non-symmetric matrix \Lambda for Directed edges
	LM := mutableMatrix(SLP,n,n);
        scan(vv,i->scan(toList dd#i, j->LM_(pos(vv,i),pos(vv,j))=l_(i,j)));
	-- print(SM);
	-- print(PM);
	-- print(LM);

        -- equate \Sigma with (I-\Lambda)^{-T}\Phi(I-\Lambda)^{-1}
	-- form ideal of relations from this matrix equation
	Linv := inverse(1-matrix(LM));
	LiPL := transpose(Linv)*matrix(PM)*Linv;
	MPmLiPL := SM-LiPL;
	J := ideal(flatten(for i from 0 to n-1 list for j from i to n-1 list MPmLiPL_(i,j)));
	-- print(MPmLiPL);
	-- print(J);
	
	-- create hash table of relations between a particular parameter t and the entries of \Sigma 
	H := new MutableHashTable;
	scan(plvars,t->H#t=eliminate(delete(t,plvars),J));
        new HashTable from H
	
	-- for t in plvars do
	-- (
      	  -- the parameter we are checking identifiability with
	  -- print(t);
	  
	  -- whether the image of the parameterization is dense in the probability space
	  -- non-zero if it is dense, 0 if it is not dense
	  -- print(min(apply(Jmt_*, q->degree(t,q))));
	  
	  -- minimum number of points in the fiber over a point in the image
	  -- print(min(delete(0,apply(Jmt_*, q->degree(t,q)))));
	  
	  -- ideal of equations containing s_(i,j) and the parameter t
	  -- print(Jmt);
	--);
)




trekSeparation = method()
    -- Input: A mixed graph containing a directed graph and a bidirected graph.
    -- Output: A list L of lists {A,B,CA,CB}, where (CA,CB) trek separates A from B.
trekSeparation MixedGraph := (g) -> (
    G := graph collateVertices g;
    dd := graph G#Digraph;
    bb := graph G#Bigraph; 
    vv := vertices g;

    -- Construct canonical double DAG cdG associated to mixed graph G
    cdG:= digraph join(
      apply(vv,i->{(a,i),join(
        apply(toList parents(G#Digraph,i),j->(a,j)),
        {(b,i)}, apply(toList bb#i,j->(b,j)))}),
      apply(vv,i->{(b,i),apply(toList dd#i,j->(b,j))}));
    aVertices := apply(vv, i->(a,i));
    bVertices := apply(vv, i->(b,i));
    allVertices := aVertices|bVertices;
    
    statements := {};
    cdC0 := new MutableHashTable;
    cdC0#cache = new CacheTable from {};
    cdC0#graph = new MutableHashTable from apply(allVertices,i->{i,cdG#graph#i});
    cdC := new Digraph from cdC0;
    for CA in (subsets aVertices) do (
      for CB in (subsets bVertices) do (
	CAbin := setToBinary(aVertices,CA);
	CBbin := setToBinary(bVertices,CB);
	if CAbin <= CBbin then (
          C := CA|CB;
	  scan(allVertices,i->cdC#graph#i=cdG#graph#i);
          scan(C, i->scan(allVertices, j->(
			 cdC#graph#i=cdC#graph#i-{j};
			 cdC#graph#j=cdC#graph#j-{i};
			 )));
	  Alist := delete({},subsetsBetween(CA,aVertices));
          while #Alist > 0 do (
	    minA := first Alist;
	    pC := reachable(cdC,set minA);
	    A := toList ((pC*(set aVertices)) + set CA);
	    Alist = Alist - (set subsetsBetween(minA,A));
	    B := toList ((set bVertices) - pC);
	    
	    -- remove redundant statements
	    if #CA+#CB < min{#A,#B} then (
	    if not ((CAbin==CBbin) and (setToBinary(aVertices,A) > setToBinary(bVertices,B))) then (
	      nS := {apply(A,i->i#1),apply(B,i->i#1),apply(CA,i->i#1),apply(CB,i->i#1)};
	      appendnS := true;
	      statements = select(statements, cS->
		if cS#0===nS#0 and cS#1===nS#1 then (
		  if isSubset(cS#2,nS#2) and isSubset(cS#3,nS#3) then 
		    (appendnS = false; true)
		  else if isSubset(nS#2,cS#2) and isSubset(nS#3,cS#3) then 
		    false
		  else
		    true)
		else if cS#2===nS#2 and cS#3===nS#3 then (
		  if isSubset(cS#0,nS#0) and isSubset(cS#1,nS#1) then 
		    false
		  else if isSubset(nS#0,cS#0) and isSubset(nS#1,cS#1) then 
		    (appendnS = false; true)
		  else
		    true)		  
		else true		
	      );
              if appendnS then statements = append(statements, nS);
            ););
     	  );
        );
      );
    );
    statements
) 

