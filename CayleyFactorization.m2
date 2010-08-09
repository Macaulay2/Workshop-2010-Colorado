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
  
  factorBrackets = (P, d, n, L) -> (
       -- INPUT: P is a bracket polynomial in Grassmannian(d,n);
       --     	 L is a list of atomic extensors of P; 
       --        each element of L is a list of indices.
       -- Output: {L', P'} where L' is the list of step d+1 extensors of P, 
       --         and P' is the result of factoring out elements of L' from P
       -- author: Josephine Yu
       -- date: August 8, 2010
       exFactors := apply(#L, i ->
	    if(#(L#i) == d+1) then (
	    l := sort toList(L#i);
	    sigma := l | sort(toList (set(0..n) - l) ); -- reorder so that indices in l comes first in the straightening order
	    permP := sub(P , matrix{permutePoints(ring P,n,sigma)}); -- apply permutation with signs
	    if(permP % (ring P)_0 == 0) then (
	    	 P = sub(permP/ring(P)_0, matrix{permutePoints(ring P,n, inversePermutation sigma)});
	    	 )
	    )
       );
       {exFactors, P}
  )
  
  permutePoints = (R, n, sigma) -> (
       -- INPUT: R is Grassmannian(*,n)
       --     	 sigma is a list of length of n, containing elements from {0,..,*}, with repetition allowed
       -- OUTPUT: list of "permuted variable"s, can be used to make a ring map
       -- author: Josephine Yu
       -- date: August 8, 2010
       apply(flatten entries vars R, v -> (
	     newIndex := apply(toList (baseName v)#1, i -> sigma#i);
     	     indicesToRingElement(R, d,n, newIndex)
	 ) 
	 )
       )
  

  indicesToRingElement = (R, d, n, indexList) -> (
      -- INPUT:  R is the ring of Grassmannian(d,n), 
      --         indexList is a list or sequence of indices between 0 and n
      --     	  The list gets sorted and appropriate sign is assigned
      --     	  If there are repeated indices, 0 is assigned
      -- OUTPUT: the Plucker variable with indices indexList
      if(#indexList == d+1 and isSubset(set indexList, set(0..n)) ) then (
    	   if(#(unique indexList) == #indexList) then (
	   	 sig := sign indexList;
       	    	 sig * sub(value ((baseName R_0)#0)_(toSequence(sort indexList)), R)
	    ) else (
	    	 sub(0, R)
    		 )
      ) else (
          print "error:  index set has wrong size or contains illegal elements";
      )
 )
  
  sign = sigma ->(
       -- Sign of a permutation
       product apply(subsets(#sigma,2), l -> (
		 if(sigma#(l#0) > sigma#(l#1)) then -1 else 1
		 )
	    )
       )

----- TEST

---- Josephie's tests
 
restart
debug loadPackage("CayleyFactorization", FileName => "/Users/bb/Documents/math/M2codes/Colorado-2010/CayleyFactorization.m2")
Grassmannian(2,5)
use((ring oo) / oo)
 P = p_(1,3,5)*p_(0,2,4)+ p_(1,2,3)*p_(0,4,5)
  P = p_(1,2,5)*p_(0,3,4)+ p_(1,2,3)*p_(0,4,5)-p_(1,3,5)*p_(0,2,4)
l = {1,2,5}
n=5;
d=2;

------ Jessica's tests

end
restart
debug loadPackage "CayleyFactorization"
R = ring Grassmannian(2,4)
L =isAtom(1,2,p_(1,2,3)*p_(2,3,4),2,4)


