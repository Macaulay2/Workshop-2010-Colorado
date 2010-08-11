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
   permutePoints(P,d,n,points) == 0_R
)	     

  -- Josephine's code:  Step 2 --
 
 ------------------- Step 2 ------------------------------------------------ 
  
  factorBrackets = (P, d, n, L) -> (
       -- INPUT: P is a polynomial in Grassmannian(d,n);
       --     	 L is a list of atomic extensors of P; 
       --        each element of L is a list of indices.
       -- Output: {L', P'} where L' is the list of step d+1 extensors of P, 
       --         and P' is the result of factoring out elements of L' from P
       topExtensors := select(L, ll -> (#ll == d+1)); -- list all step d+1 extensors 
       productFactors := product apply(topExtensors , l -> ( indicesToRingElement(ring P, d, n, sort toList(l))) ); -- convert them into variables in ring of P and take product
       if(P % productFactors == 0) then (
        {topExtensors, P/productFactors}
       ) else (
         print("error: the input polynomial is not divisible by the given bracket variables");
       	 null
       )
      )

   ------------------- Step 3 and 4 ------------------------------ 

 findPairFactor = (P, d, n, L) -> (
      -- INPUT: P is a polynomial in Grassmannian(d,n);
      --     	 L is a list of atomic extensors of P; 
      -- OUTPUT: A pair (E,F) such that E ^ F is a primitive factor of P
      -- Method: Step 3 & 4 in Algorithm 3.5.6 of Sturmfels' Algorithmic Inv. Theory
      atomicExt := select(L, ll-> (#ll =!= d+1));
      scan(subsets(#atomicExt,2), a -> (
		E := sort toList atomicExt#(a#0);
		F := sort toList atomicExt#(a#1);
		if(#E + #F > d+1) then (
		     newOrder := inversePermutation(sort(E) | sort(F) | sort toList(set(0..n) - (E|F))); 
		     PermP := permutePoints(P, d,n, newOrder); -- permute the indices so that E and F comes first
		     found := 1;
		     scan(terms PermP, monomial -> (
			  supp := (support(monomial))_{0,1};
			  firstRow := set (baseName(supp#0))#1; --first row of tableau
			  secondRow := set (baseName(supp#1))#1; -- second row of tableau
			  if((not isSubset(set(0..#E-1),firstRow)) or (not isSubset(set(0..#F-1), firstRow+secondRow)) or (not isSubset(firstRow, set(0..#E+#F-1) ))) then (
			      print(firstRow, secondRow);
     	       	    	      found = 0;
			      break;
			       )
			  )
		     );
		     if(found == 1) then  (
			  newIndices := toList(0..(#E + #F - d -2));
			  substitutions := select( apply(unique flatten ((terms PermP) / support), v -> (
			       ind := toList (baseName v)#1;
			       if(isSubset(ind, set(0..#E+#F-1))) then (
				    if(ind == toList(0..d)) then (v => 1)
				    else(v => 0) -- this kills all except the first representative (the one with p_(0..d)) in the dotted expression
				    )
			       else (
				    dif := toList((set ind)-set(#E..#E+#F-1));
				    if(#dif < #ind) then ( -- if the index intersects with F (after permutation)
					 v => indicesToRingElement(ring P, d, n, newIndices|dif)
					 )
		               	    )
			       )
		     	  ), a -> a =!= null);
		     	  inverseNewOrder := sort(E) | sort(F) | sort toList(set(0..n) - (E|F));
		     	  break({{E,F}, permutePoints(sub(P, substitutions), d, n, inverseNewOrder), apply(toList(0..(#E + #F - d -2)), i -> inverseNewOrder_i)});    
		     )
	  	)
      )
  )
)


  
   -------------------- Auxiliary functions ---------------------------------

  permutePoints = method();
  permutePoints(Ring, ZZ, ZZ, List) := List => (R,d, n, sigma) -> (
       -- INPUT: R is coordinate ring of Grassmannian(d,n)
       --     	 sigma is a list of length of n, containing elements from {0,..,d}, with repetition allowed
       -- OUTPUT: list of "permuted variable"s, can be used to make a ring map
       apply(flatten entries vars R, v -> (
     	     indicesToRingElement(R, d,n, apply(toList (baseName v)#1, i -> sigma#i))
	 ) 
	 )
       )
  permutePoints (RingElement, ZZ, ZZ, List) := RingElement => (P, d, n, sigma) -> (
   	-- INPUT:  P is a polynomial in coordinate ring of Grassmannian(d,n), sigma as above
	-- OUTPUT:  another polynomial in same variables, after substitution
	-- This one does substitutions only for the variables appearing in the polynomial P
      sub(P, apply(unique flatten ((terms P) / support), v -> (
			     v => indicesToRingElement(ring P, d,n, apply(toList (baseName v)#1, i -> sigma#i))
     	       	    	       )
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
    	   if(#(set indexList) == #indexList) then (
	   	 sig := sign indexList;
       	    	 sig * sub(value ((baseName R_0)#0)_(toSequence(sort indexList)), R)
	    ) else (
	    	 sub(0, R)
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
-------------------  the main function -------------------------
 ------------------------------------------------------------------- 

cayleyFactor = method();
cayleyFactor(RingElement, ZZ, ZZ) := List => (P,d,n) -> (
     cayleyFactor(P,d,n, toList apply(0..n, i-> set {i}))
     )
cayleyFactor(RingElement, ZZ, ZZ, List) := Expression => (P,d,n,partialAtoms) -> (
     if((degree P)#0 <= 0) then (return(P));
     knownFactors := null;
     atoms := toList listAtoms(P, partialAtoms, d, n); -- Step 1
     if(#select(atoms, a -> #a >= d+1) <= 0 and (max apply(subsets(atoms,2), S-> #S#0+#S#1)) < d+1) then (
	  print("atom size ",(max apply(subsets(atoms,2), S-> #S#0+#S#1)));
	  print("not factorable, step 1. P = ", P, "atoms = ", atoms);
	  return(null);
	  ); 
     pureFactors := factorBrackets(P,d,n,atoms); -- Step 2
     if(#pureFactors#0 > 0) then (
    	  knownFactors = flatten sequence apply(pureFactors#0, a -> sort toList a);
       	  P = pureFactors#1;
       	  atoms = toList((set atoms) - (set pureFactors#0));
	  if(#atoms == 0 or (degree P)#0 <= 0)then (
	       print( "after step 2: ", knownFactors);
	       return(knownFactors);
	       )
       	  );
     pairFactor := findPairFactor(P,d,n,atoms); -- Steps 3 and 4
     if(pairFactor === null) then (
	  	  print("not factorable, step 3. P = ", P, "atoms = ", atoms);
	  return(null);
	  );
     if(knownFactors === null) then (
	  knownFactors = flatten sequence pairFactor#0;
       	  ) else (
	  knownFactors = (knownFactors, flatten sequence pairFactor#0);
	  );
     newIndices := pairFactor#2;
     newPartialAtoms := toList((set atoms) - (set (pairFactor#0 / set))) | {set newIndices};
     expansionKey := { replace("[{}]", "",toString(sort toList newIndices)), toString flatten sequence pairFactor#0};
     print("trying to factor ", toString pairFactor#1);
     print("new partial atoms: ", newPartialAtoms);
     smallerFactors := cayleyFactor(pairFactor#1, d,n, newPartialAtoms);
     if(smallerFactors === null) then (
	 print("not factorable, recursive step. P = ", P, "atoms = ", atoms);
	  return(null);
	  ) else (
	  print("smaller Factors: ", smallerFactors);
	  print("after substitution: ", replace(expansionKey#0, expansionKey#1, toString smallerFactors));
     	  return(value replace(expansionKey#0, expansionKey#1, toString smallerFactors));
	  );
     )
           

{*
cayleyFactor(RingElement, ZZ, ZZ, List) := List => (P,d,n, partialAtomicExt) -> (
     L := toList listAtoms(P,partialAtomicExt, d,n);
     if(set(L) == set(partialAtomicExt) or max apply(subsets(L,2), S-> #S#0+#S#1) < d+1) then (
	  print "NOT FACTORABLE";
	  null
	  ) else (
        	  pureFactors := factorBrackets(P,d,n,toList L); -- Step 2
     	  	  P = pureFactors#1;
     	  	  if(degree(P)#0 == 0) then (pureFactors#0|{1_R})
	  	  else (
	       	       pairFactor := findPairFactor(P,d,n,L); -- Step 3
		       if(pairFactor == null) then (
			    	  print "NOT FACTORABLE";
	  			  null
			    ) else (
     		       	    newIndices := set(0..(#pairFactor#1#0+#pairFactor#1#1-d-2));
     		       	    newPartialAtomicExt := append(drop(L, pairFactor#0), newIndices);    
			    pairFactor#1 | cayleyFactor(pairFactor#2, newPartialAtomicExt, d,n)
			    )
     	  	       )
     		  )
)

*}


 ------------------------------------------------------------------- 


----- TEST

---- Josephie's tests
end

restart
debug loadPackage("CayleyFactorization", FileName => "/Users/bb/Documents/math/M2codes/Colorado-2010/CayleyFactorization.m2")
d = 2; n=5;
Grassmannian(d,n);
use((ring oo) / oo);
partialAtoms = toList apply(0..n, i->set {i})
 P = p_(1,3,5)*p_(0,2,4)+ p_(1,2,3)*p_(0,4,5)
  P = p_(1,2,5)*p_(0,3,4)+ p_(1,2,3)*p_(0,4,5)-p_(1,3,5)*p_(0,2,4)
 P = p_(0,1,2)*p_(3,4,5)*(  p_(1,3,5)*p_(0,2,4)+ p_(1,2,3)*p_(0,4,5));
cayleyFactor(P,d,n)
 
l = {1,2,5}
n=5;
d=2;
L = {{0,1,2},{1,3},{3,4,5},{0,1,4,5},{1,3,5}};
L = {{0,1,2},{1,3},{3,4,5},{0,1,4,5}};
L = subsets(n+1,d-1)| subsets(n+1,d) | {{0,1,2},{3,4,5}}
factorBrackets(P, d, n, L)
E = {0,2}; F = {1,4};

d=2;n=8;
Grassmannian(d,n);
use((ring oo) / oo);
partialAtoms = toList apply(0..n, i->set {i})
P = p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8);
P = -p_(0,4,6)*p_(5,7,8)+p_(0,4,5)*p_(6,7,8);
P =  -p_(2,7,8);
cayleyFactor(P,d,n)
L=listAtoms(P, 2, 8);
L = apply((toList L),a->toList a)
L = reverse L
factorBrackets(P,d,n,toList L) 
findPairFactor(P,d,n,toList L)
sigma = {2,3,0,1,5,7,6,8,4}
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


