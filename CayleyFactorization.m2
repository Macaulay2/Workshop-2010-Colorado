newPackage(
	"CayleyFactorization",
    	Version => "0.1", 
    	Date => "August 8, 2010",
    	Authors => {
	     {Name => "Jessica Sidman", Email => "jsidman@mtholyoke.edu", HomePage => "http://www.mtholyoke.edu/~jsidman"},
	     {Name => "Josephine Yu", Email => "josephine.yu@math.gatech.edu", HomePage => "http://people.math.gatech.edu/~jyu67"}
	     },
    	Headline => "Cayley Factorization",
    	DebuggingMode => true
    	)
   
   export{isAtom}
   -- Jessica's code:  Step 1 --
   ----------------------------------------------------
 {*  
   listAtoms := (P, d, n) ->(
	--INPUT:  P = bracket polynomial of rank d+1 in n+1 points, d, n
	--OUTPUT: AtomicExt = list of equivalence classes of points.  Each equivalence class is an atomic extensor.
	
	--points = list of the n+1 points
	points:= toList(0..n);
	
	--AtomicExt
	AtomicExt := {};
	
	 
	--while points is nonempty
	
	--call isAtom(points_0, points_1, P, d, n)
	
	)
   *}

   rep = (a,b,L)-> (for x in L list (if x==a then b else x))
   
   isAtom = (a,b,P,d,n) ->(
	--INPUT: a,b = distinct numbers between 1 and n,
	--P = bracket polynomial of rank d+1 in n+1 points, d, n
	--OUTPUT: 1 if a join b is an atomic extensor, 0 otherwise	
	R := ring P;	
	--list the subcripts of all of the variables in order
	S:=new MutableList from apply(flatten entries vars R , p ->(baseName p)#1);
	SLength:=#S;
	for i from 0 to (SLength-1) do (
	     --replace S_i by 0_R if a and b are in
	     if isSubset({a,b}, S#i) then S#i = 0_R
	     --replace b by a in S_i and then replace S_i by sign of permutation* p_(S_i)
	     else if isSubset({b}, S#i) then 
	       ( tempR := rep(a,b,S#i);
	      	S#i= sign(tempR)*((baseName R_0)#0)_(toSequence sort(tempR)))
	     else S#i=((baseName R_0)#0)_(S#i);
	     );
     	  f:=map(R,R, toList S);
	  f(P)==0_R
)	     
	     
       

   
  -- Josephine's code:  Step 2 --
  
  factorBrackets := (P, d, n, L) -> (
       -- INPUT: P is a bracket polynomial in Grassmannian(d,n);
       --     	 L is a list of atomic extensors of P; 
       --        each element of L is a list of indices.
       -- Output: (L', P') where L' is the list of step d+1 extensors of P, 
       --         and P' is the result of factoring out elements of L' from P
       -- author: Josephine Yu
       -- date: August 8, 2010
       apply(#L, i ->
	    l := sort toList(L#i);
	    sigma := l | sort(toList (set(0..n) - l) );
	    apply(flatten entries vars ring P, p -> (
		     varName := (baseName p)#0;
		     newIndex := apply(toList (baseName p)#1, i -> sigma#i);
		     sig = sign newIndex;
		     sub(((basename p)#0)_toSequence(newIndex), ring P)
		 ) 
		 );
	    )
       
       )
  
  permuteAndStraighten := (P, d, n, sigma) -> (
       -- INPUT: P is a bracket polynomial in Grassmannian(d,n)
       --     	 sigma is a permutation of 0..n (encoded as a list)
       -- OUTPUT: Result the straightening algorithm with permuted variables
       -- author: Josephine Yu
       -- date: August 8, 2010
       
       )
  
  sign = sigma ->(
       -- Sign of a permutation
       product flatten table(#sigma, #sigma, (i,j) -> (
		 if(i < j and sigma#i > sigma#j) then -1 else 1
		 )
	    )
       )
end
restart
debug loadPackage "CayleyFactorization"
R = ring Grassmannian(2,4)
L =isAtom(1,2,p_(1,2,3)*p_(2,3,4),2,4)

