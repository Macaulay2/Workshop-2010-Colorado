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
   
   
   -- Jessica's code:  Step 1 --
   
   
   
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
  
  sign := sigma ->(
       -- Sign of a permutation
       product flatten table(#sigma, #sigma, (i,j) -> (
		 if(i < j and sigma#i > sigma#j) then -1 else 1
		 )
	    )
       )
