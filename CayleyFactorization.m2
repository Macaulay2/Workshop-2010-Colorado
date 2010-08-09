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
   
   export{isAtom, listAtoms}
   -- Jessica's code:  Step 1 --
   ----------------------------------------------------
   listAtoms = method()
     
   listAtoms(RingElement, ZZ, ZZ) := (P, d, n) ->(
	--INPUT:  P = bracket polynomial of rank d+1 in n+1 points, d, n
	--OUTPUT: AtomicExt = list of equivalence classes of points.  Each equivalence class is an atomic extensor.
       	--Jessica Sidman, August 9, 2010
	R:= ring P;
	
      	--points = list of the n+1 points
	points:= new MutableList from (0..n);
	
	--AtomicExt 
	AtomicExt := new MutableList from {};
	
	numPoints :=0;
	atomicClass :=set{};
	
	while (#points) > 0 do(
	     currentPoint := points#0;
	     --create a temporary set containing the current element of points
	     atomicClass= set{currentPoint};
	     points = drop(points, {0,0});
	     numPoints = #points;
	     
	     for i from 0 to (#points-1) do(
		  if isAtom(currentPoint, points#i, P, d,n) then atomicClass=atomicClass+set{points#i}
		  );
	     points = new MutableList from toList ((set toList points) -atomicClass);
	     AtomicExt = append(AtomicExt, atomicClass);
	     );
	AtomicExt
		)

 listAtoms(RingElement, List, ZZ, ZZ) := (P, partialAtomsInput, d, n) ->(
	--INPUT:  P = bracket polynomial of rank d+1 in n+1 points, partialAtoms = MutableList whose elements are sets of points already known to be in the same equivalence class, d, n
	--OUTPUT: AtomicExt = list of equivalence classes of points (consisting of unions of the elements in partialAtoms.  Each equivalence class is an atomic extensor.
       	--Jessica Sidman, August 9, 2010
	R:= ring P;
	
	partialAtoms:= new MutableList from partialAtomsInput;
	
	--AtomicExt 
	AtomicExt := new MutableList from {};
	
	atomicClass :=set{};
	
	while (#partialAtoms) > 0 do(
	     --take the first element of partialAtoms
	     currentAtom := partialAtoms#0;
	     
	     --the currentAtom is a set.  We'll use it to form a new atomicClass
	     atomicClass = currentAtom;
	     
	     --remove this atomic class from the list of partialAtoms
	     partialAtoms = drop(partialAtoms, {0,0});
	  
	     --Determine if this AtomicClass should contain more elements by testing to see if its first element is in the same atomic class as the first elment of 
	     --each element in the partialAtoms list
	     temporaryAtoms := partialAtoms; 
	     for i from 0 to (#temporaryAtoms-1) do(
		  if isAtom((toList currentAtom)_0, ((toList temporaryAtoms#i))_0, P, d,n) then (
		       atomicClass=atomicClass+temporaryAtoms#i;
		       partialAtoms = new MutableList from toList( (set toList partialAtoms) - {temporaryAtoms#i});
		  );
	     );
	     AtomicExt = append(AtomicExt, atomicClass);
	     );
	AtomicExt
	)
	     
	   
	   
   rep = (a,b,L)-> (for x in L list (if x==a then b else x))
   
   isAtom = (a,b,P,d,n) ->(
	--INPUT: a,b = distinct numbers between 1 and n,
	--P = bracket polynomial of rank d+1 in n+1 points, d, n
	--OUTPUT: 1 if a join b is an atomic extensor, 0 otherwise	
	R := ring P;	
	--list the subcripts of all of the variables in order
{*	S:=new MutableList from apply(flatten entries vars R , p ->(baseName p)#1);
	SLength:=#S;
	for i from 0 to (SLength-1) do (
	     --replace S_i by 0_R if a and b are in
	     if isSubset({a,b}, S#i) then S#i = 0_R
	     --replace b by a in S_i and then replace S_i by sign of permutation* p_(S_i)
	     else if isSubset({b}, S#i) then 
	       ( tempR := rep(a,b,S#i);
	      	S#i= sign(tempR)*sub(value (((baseName R_0)#0)_(toSequence sort(tempR))), R))
	     else S#i=sub(value ((baseName R_0)#0)_(S#i), R) ;
	     );
	*}
   points:= toList (0..n);
   points = replace(a,b,points);
   S = permutePoints(R,d,n,points);
     	  f:=map(R,R, toList S);
	  f(P)==0_R
)	     

  -- Josephine's code:  Step 2 --
 
 ------------------- Step 2 ------------------------------------------------ 
  
  factorBrackets = (P, d, n, L) -> (
       -- INPUT: P is a polynomial in Grassmannian(d,n);
       --     	 L is a list of atomic extensors of P; 
       --        each element of L is a list of indices.
       -- Output: {L', P'} where L' is the list of step d+1 extensors of P, 
       --         and P' is the result of factoring out elements of L' from P
       -- author: Josephine Yu
       -- date: August 8, 2010
       extensorFactors := apply( select(L, ll -> (#ll == d+1)), l -> ( indicesToRingElement(ring P, d, n, sort toList(l))) ); -- list all step d+1 extensors and convert them into variables in ring of P
       productFactors := product extensorFactors;
       if(P % productFactors == 0) then (
    	 P = P/productFactors; 
        {extensorFactors, P}
       ) else (
       	 print("error: the input polynomial is not divisible by the given bracket variables");
       )
      )

   ------------------- Step 3 ------------------------------------------------ 

 findPairFactor = (P, d, n, L) -> (
      -- INPUT: P is a polynomial in Grassmannian(d,n);
      --     	 L is a list of atomic extensors of P; 
      -- OUTPUT: A pair (E,F) such that E ^ F is a primitive factor of P
      -- Method: Step 3 in Algorithm 3.5.6 of Sturmfels' Algorithmic Inv. Theory
      atomicExt := select(L, ll-> (#ll =!= d+1));
      scan(subsets(#atomicExt,2), a -> (
		E := atomicExt#(a#0);
		F := atomicExt#(a#1);
		if(#E + #F > d+1) then (
		     newOrder := sort(E) | sort(F) | sort toList(set(0..n) - (E|F)); 
		     PermP := sub(P, matrix{permutePoints(ring P, d,n, newOrder)});
		     found := 1;
		     scan(terms PermP, monomial -> (
			  supp := (support(monomial))_{0,1};
			  firstRow := set (baseName(supp#0))#1; --first row of tableau
			  secondRow := set (baseName(supp#1))#1; -- second row of tableau
			  if((not isSubset(E,firstRow)) or (not isSubset(F, firstRow+secondRow))) then (
     	       	    	      found = 0;
			      break;
			       )
			  )
		     );
		     if(found == 1) then  (
		     	  break({E,F});
		     );
	  	)
      )
  )
)
  
   -------------------- Auxiliary functions ---------------------------------

  
  permutePoints = (R,d, n, sigma) -> (
       -- INPUT: R is Grassmannian(d,n)
       --     	 sigma is a list of length of n, containing elements from {0,..,d}, with repetition allowed
       -- OUTPUT: list of "permuted variable"s, can be used to make a ring map
       -- author: Josephine Yu
       -- date: August 8, 2010
       apply(flatten entries vars R, v -> (
	     newIndex := apply(toList (baseName v)#1, i -> sigma#i);
     	     indicesToRingElement(R, d,n, newIndex)
	 ) 
	 )
       )
  
 ------------------------------------------------------------------- 

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
  
   ------------------------------------------------------------------- 

  sign = sigma ->(
       -- Sign of a permutation
       product apply(subsets(#sigma,2), l -> (
		 if(sigma#(l#0) > sigma#(l#1)) then -1 else 1
		 )
	    )
       )

 ------------------------------------------------------------------- 


----- TEST

---- Josephie's tests
end

restart
debug loadPackage("CayleyFactorization", FileName => "/Users/bb/Documents/math/M2codes/Colorado-2010/CayleyFactorization.m2")
Grassmannian(2,5);
use((ring oo) / oo);
 P = p_(1,3,5)*p_(0,2,4)+ p_(1,2,3)*p_(0,4,5)
  P = p_(1,2,5)*p_(0,3,4)+ p_(1,2,3)*p_(0,4,5)-p_(1,3,5)*p_(0,2,4)
 P = p_(0,1,2)*p_(3,4,5)*(  p_(1,3,5)*p_(0,2,4)+ p_(1,2,3)*p_(0,4,5));
l = {1,2,5}
n=5;
d=2;
L = {{0,1,2},{1,3},{3,4,5},{0,1,4,5},{1,3,5}};
L = {{0,1,2},{1,3},{3,4,5},{0,1,4,5}};
L = subsets(n+1,d-1)| subsets(n+1,d) | {{0,1,2},{3,4,5}}
factorBrackets(P, d, n, L)
E = {0,2}; F = {1,4};

d=2;n=8;
R = ring Grassmannian(2,8);
P = p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8)
L=listAtoms(P, 2, 8)
L = apply((toList L),a->toList a)
factorBrackets(P,d,n,toList L) 
findPairFactor(P,d,n,L)
------ Jessica's tests

end
restart
debug loadPackage "CayleyFactorization"
R = ring Grassmannian(2,5)

L = listAtoms(p_(0,1,2)*p_(3,4,5)+p_(0,1,3)*p_(2,4,5),2,5)

R = ring Grassmannian(2,8)

L=listAtoms(p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8), 2, 8)
toList L

K = listAtoms(p_(0,4,5)*p_(6,7,8)-p_(0,4,6)*p_(5,7,8), {set {0}, set {7, 8}, set {4}, set {5, 6}}, 2, 8)

toList K     
isAtom(0,4, p_(0,4,5)*p_(6,7,8)-p_(0,4,6)*p_(5,7,8),2,8)

isAtom(2,3,p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8), 2, 8)

isAtom(4,5,p_(0,1,2)*p_(3,4,5)+p_(0,1,3)*p_(2,4,5),2,5)

L =isAtom(0,0,p_(1,2,3)*p_(2,3,4),2,4)


