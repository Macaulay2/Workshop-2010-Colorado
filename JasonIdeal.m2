newPackage(
     "JasonIdeal",
     Version => "0.1",
     DebuggingMode => true
     )

--======================--

export{JJ,socleCheck,jasonIdeal,BaseField}

--======================--

-- NEEDS COMMENTS
--
--
-- General code to find family of ideals of large projective dimenson
-- input: g = number of generators
--     	  M = list
-- output: Ideal with high prjective dimension
--
-- Note: if #M = 1 then us function K below
--       g >= 2, #M >= 2
JJ = method( Options => { BaseField => QQ} )
JJ(ZZ,List) := opt -> (g,M) -> ( 
     n := #M;
     if n == 1 
     then ( I = jasonIdeal(g,1,M_0+1);	  
	   )
     else (
     	  d := i -> sum(take(M, -(n - i)-1))+1;	  
     	  ZZ[t_1..t_g];
     	  m := last M;  
     	  ind := (g,M) ->  apply(apply( toList fold((i,j) -> i**j,
	  	append(
     		     apply(drop(M,-1), m -> 
	  		  set flatten apply(select(terms product(1..g, j -> 
			 		 sum(m, i -> t_j^i)), i -> 
		    		    first degree i == m),exponents)),
     		     set flatten apply(select(terms product(1..g, j -> sum(m+1, i -> t_j^i)), 
	       		       i -> first degree i == m),exponents)))/deepSplice,toList),i -> transpose matrix i);     
          front := (g,M) ->if #M == 1 then apply(flatten apply(M, m -> flatten apply(select(terms product(1..g, j -> 
			 	   sum(m, i -> t_j^i)), i -> 
		    	      first degree i == m), exponents)),i->transpose matrix {i}) else apply(apply( toList fold((i,j) -> i**j,
     	       		 apply(M, m -> set flatten apply(select(terms product(1..g, j -> 
			 		     sum(m, i -> t_j^i)), i -> 
		    			first degree i == m),
	       			   exponents)))
     		    /deepSplice,toList),i -> transpose matrix i);
     	  middle := (i,g,M) -> (
	       A := mutableMatrix(ZZ,g,2);
	       A_(0,0) = M_(i); --was i+1	    
	       A_(0,1) = d(i+2);
	       {matrix A}|toList(apply (0..g-2, i-> matrix rowSwap(A,i,i+1)))
	       );
     	  matrixListPre := flatten toList apply(1..n-2, -- change to 0 to n-3
	       i -> flatten apply(front(g,take(M,i)),j -> flatten apply(middle(i,g,M), k -> j|k)));
     	  matrixList := apply(middle(0,g,M)|matrixListPre, i -> i | map(ZZ^g, ZZ^(n-rank source i), 0));
          k := opt.BaseField;
	  indList := ind(g,M);
	  v := (toList (x_(1,1)..x_(n,g))) | apply(indList, i -> z_i);
	  B = k[v,MonomialOrder=>Lex];
	  --B = k[v];
	  I = ideal(apply(x_(1,1)..x_(1,g), i -> i^(d 1)),sum apply(matrixList,m-> product flatten for i to g-1 list ( for j to n-1 list x_(j+1,i+1)^(m_(i,j))))+sum apply(indList,m-> (product flatten for i to g-1 list ( for j to n-1 list x_(j+1,i+1)^(m_(i,j))))*z_m));
     	  I.cache.gen = g;
     	  I.cache.num = n;
	  I.cache.socle = product( x_(1,1)..x_(n,g), deepSplice{ apply ( 1..n,i-> g:(d(i)-1) )},  (i,j) -> i^j )
	  );
     I
)     


-- input: Ideal J(g,M)
-- ouput: Sets variables z to zero.
--
truncJ = method()
truncJ(Ideal) := (I) -> (
     f=map(ZZ/5051[x_(1,1)..x_(I.cache.gen,I.cache.num)],ring I);
     f(I)
     )

-- Gives Jason's ideal and is the special case of function J above.  
-- input: m = number of generators minus n ( m = g )
--     	  n = number of times to include y's
-- 	  d = degree of the generators
-- output: ideal with large progective dimension.
--
-- note: to compute J(g,{m}) use K(g,1,m+1)
--
jasonIdeal = method()
jasonIdeal(ZZ,ZZ,ZZ) := (m,n,d) -> (
    A := ZZ/5051[x_1..x_m];
    L := flatten entries basis(d-1,A);
    l := length L;
    B = ZZ/5051[x_1..x_m,z_(1,1)..z_(l,n)]; -- not a local variable
    I = ideal apply(x_1..x_m, i -> i^d) + ideal apply(1..n, k -> sum(1..l, j -> sub(L_(j-1),B)*z_(j,k)));
    I.cache.gen = m;
    I.cache.num = n;
    I.cache.socle = product( x_1..x_m, m:(d-1), (i,j) -> i^j );
    I
    )

socleCheck = method()
socleCheck(Ideal) := (I) -> (
     s := I.cache.socle;
     if (s%I) == 0 then return false;
     all(gens ring I, i -> ((i*s)%I) == 0)
     );

socleCheck(Ideal, RingElement) := (I,s) -> (
     if (s%I) == 0 then return false;
     all(gens ring I, i -> ((i*s)%I) == 0)
     );
