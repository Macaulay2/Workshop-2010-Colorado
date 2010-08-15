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
   
   export{cayleyFactor, GrassmannCayleyAlgebra, straightenPoly}
   
   
------------------------------------------------------------------- 
-------------------  the main function -------------------------
------------------------------------------------------------------- 

	   
-- INPUT:  P, a multilinear bracket expression, i.e. an element of coord. ring of Gr(d,n)
--     	      where each element of 0..n appears exactly once in each monomial
-- OUTPUT:  null, if P is not Cayley-factorable.  Otherwise, output the Cayley factorization.
--     	    (,) denotes "meet" and {,} denotes "join"
-- WARNING:  We assume is P is already an element of the coordinate ring of Gr(d,n)

cayleyFactor = method(     
     TypicalValue => Expression, 
     Options => { 
     	  OnlineStraightening => true
	  });
cayleyFactor(RingElement, ZZ, ZZ) := Expression => o -> (P,d,n) -> (
     cayleyFactor(P,d,n, toList apply(0..n, i-> set {i}))
     )
cayleyFactor(RingElement, ZZ, ZZ, List) := Expression => o -> (P,d,n,partialAtoms) -> (
     if((degree P)#0 <= 0) then (return(P));
     knownFactors := null;
     atoms := toList listAtoms(P, partialAtoms, d, n,o); -- Step 1
     if(#select(atoms, a -> #a >= d+1) <= 0 and (max apply(subsets(atoms,2), S-> #S#0+#S#1)) < d+1) then (
--	  print("atom size ",(max apply(subsets(atoms,2), S-> #S#0+#S#1)));
--	  print("not factorable, step 1. P = ", P, "atoms = ", atoms);
	  return(null);
	  ); 
     pureFactors := factorBrackets(P,d,n,atoms, o); -- Step 2
     if(#pureFactors#0 > 0) then (
    	  knownFactors = flatten sequence apply(pureFactors#0, a -> sort toList a);
       	  P = pureFactors#1;
       	  atoms = toList((set atoms) - (set pureFactors#0));
	  if(#atoms == 0 or (degree P)#0 <= 0)then (
--	       print( "after step 2: ", knownFactors);
	       return(knownFactors);
	       )
       	  );
     pairFactor := findPairFactor(P,d,n,atoms, o); -- Steps 3 and 4
     if(pairFactor === null) then (
--	  	  print("not factorable, step 3. P = ", P, "atoms = ", atoms);
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
 --    print("trying to factor ", toString pairFactor#1);
 --    print("new partial atoms: ", newPartialAtoms);
 --    print("expansionKey: ", expansionKey);
     smallerFactors := cayleyFactor(pairFactor#1, d,n, newPartialAtoms);
     if(smallerFactors === null) then (
--	 print("not factorable, recursive step. P = ", P, "atoms = ", atoms);
	  return(null);
	  ) else (
--	  print("smaller Factors: ", smallerFactors);
--	  print("after substitution: ", replace(expansionKey#0, expansionKey#1, toString smallerFactors));
     	  return(value replace(expansionKey#0, expansionKey#1, toString smallerFactors));
	  );
     )
           
	   
	   
 ------------------------------------------------------------------- 
 --------------- Grassmann-Cayley algebra ---------------------------
 -------------------------------------------------------------------

meet = method()

GrassmannCayleyAlgebra =  method(
     TypicalValue => Ring, 
     Options => { 
	  CoefficientRing => ZZ, 
	  PointName => symbol a,
	  BasisChoice => symbol e,
	  PluckerVariable => symbol p
	  });

GrassmannCayleyAlgebra (ZZ,ZZ) := o -> (d,n) -> (
      a := o.PointName;
      e := o.BasisChoice;
      p := o.PluckerVariable;
      G := Grassmannian(d,n, CoefficientRing => o.CoefficientRing, Variable => p);
      R := ring(G)/G;
      E := o.CoefficientRing[a_0..a_n, e_0..e_d, SkewCommutative => true];
      GC0 := E ** R;
      use(GC0);      
      I := ideal apply(a_0..a_n, v-> v_GC0* product(apply(toList(e_0..e_d), ee -> ee_GC0))) + 
     ideal apply(subsets(0..n,d+1),s-> (p_(toSequence(sort toList s)))_GC0*product(apply(toList(e_0..e_d), ee->ee_GC0))- product apply(s, i-> (a_i)_GC0));
     GC := GC0/I;
      
     meet(GC, GC) := (A,B) -> (
      termsA := terms A;
      termsB := terms B;
      if(#termsA > 1) then (
	   return(meet(termsA#0, B) + meet(sum drop(termsA, {0,0}),B)); 
	   );
      if(#termsB > 1) then (
      	   return(meet(A, termsB#0) + meet(A, sum drop(termsB, {0,0}))); 
	   );
      monoA := termsA#0;
      monoB := termsB#0;
      degA := (degree(monoA))#0;
      degB := (degree(monoB))#0;
      if(degA + degB < d+1) then (return(0));
      sum apply(subsets(degA , d+1 - degB), S -> (
		coeffA := (first listForm(monoA))#1;
		insideA := sort toList S;
		outsideA := sort toList (set(0..degA-1) - S);
     	        signShuffle := signOfShuffle(insideA,outsideA);
		insideMonoA := product apply(insideA, i -> (support monoA)#i); 
		outsideMonoA := product(set(support monoA) - {insideMonoA});
		bracket :=insideMonoA*monoB;
		if(bracket == 0) then (0)
		else (
		     bracketCoeff :=  (first listForm(bracket))#1;
		     bracket = product drop(support(bracket),{0,d});
		     signShuffle*coeffA*bracketCoeff*bracket*outsideMonoA
		     )
		)	   
	   )
      );
 GC
      )
 
 
 
 
 


 
	   

   ----------------------------------------------------
 -----------------Step 1 functions ---------------------
   ----------------------------------------------------

   listAtoms = method(     
	Options => { 
     	  OnlineStraightening => true
	  })
     
   listAtoms(RingElement, ZZ, ZZ) := o-> (P, d, n) ->(
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
		  if isAtom((currentPoint, points#i), P, d,n, o) then atomicClass=atomicClass+set{points#i}
		  );
	     points = new MutableList from toList ((set toList points) -atomicClass);
	     AtomicExt = append(AtomicExt, atomicClass);
	     );
	AtomicExt
		)

 listAtoms(RingElement, List, ZZ, ZZ) := o-> (P, partialAtomsInput, d, n) ->(
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
		  if isAtom(((toList currentAtom)_0, ((toList temporaryAtoms#i))_0), P, d,n,o) then (
		       atomicClass=atomicClass+temporaryAtoms#i;
		       partialAtoms = new MutableList from toList( (set toList partialAtoms) - {temporaryAtoms#i});
		  );
	     );
	     AtomicExt = append(AtomicExt, atomicClass);
	     );
	AtomicExt
	)
	     
	   
	   
   rep = (a,b,L)-> (for x in L list (if x==a then b else x))
   
   isAtom = method(     
	Options => { 
     	  OnlineStraightening => true
	  })
   isAtom(Sequence,RingElement,ZZ,ZZ) := Boolean => o-> (pair,P,d,n) -> (
	--INPUT: a,b = distinct numbers between 1 and n,
	--P = bracket polynomial of rank d+1 in n+1 points, d, n
	--OUTPUT: 1 if a join b is an atomic extensor, 0 otherwise	
	R := ring P;	
	(a,b) := pair;
   	points:= toList (0..n);
   	points = replace(a,b,points);
   	if(o.OnlineStraightening)then(
	     return(straightenPoly(permutePoints(P,d,n,points),d,n) == 0_R)
	     )else(return(permutePoints(P,d,n,points) == 0_R));
	)	     

 
 ------------------- Step 2 ------------------------------------------------ 
  factorBrackets=method(     
       Options => { 
     	  OnlineStraightening => true
	  })
  factorBrackets(RingElement,ZZ,ZZ,List) := List => o-> (P, d, n, L) -> (
       -- INPUT: P is a polynomial in Grassmannian(d,n);
       --     	 L is a list of atomic extensors of P; 
       --        each element of L is a list of indices.
       -- Output: {L', P'} where L' is the list of step d+1 extensors of P, 
       --         and P' is the result of factoring out elements of L' from P
       R := ring P;
       topExtensors := select(L, ll -> (#ll == d+1)); -- list all step d+1 extensors 
       productFactors := product apply(topExtensors , l -> ( indicesToRingElement(R, d, n, sort toList(l))) ); -- convert them into variables in ring of P and take product
       if(o.OnlineStraightening) then (
	    allFactoredAtoms := sort flatten apply(topExtensors, l->sort toList(l));
	    newOrder := inversePermutation(allFactoredAtoms | sort toList( set(0..n) - allFactoredAtoms ) );
	    {topExtensors, straightenPoly( lift( permutePoints(
		 straightenPoly(permutePoints(P, d, n, newOrder),d,n)/permutePoints(productFactors, d, n, newOrder), 
		 d, n, allFactoredAtoms | sort toList( set(0..n) - allFactoredAtoms )), R),d,n)}
	    ) else (
       	    {topExtensors, P/productFactors}--straightening is used
       	    )
       )

   ------------------- Step 3 and 4 ------------------------------ 

findPairFactor = method(     
     Options => { 
     	  OnlineStraightening => true
	  })
 findPairFactor(RingElement,ZZ,ZZ,List) := List => o -> (P, d, n, L) -> (
      -- INPUT: P is a polynomial in Grassmannian(d,n);
      --     	 L is a list of atomic extensors of P; 
      -- OUTPUT: A pair (E,F) such that E ^ F is a primitive factor of P
      -- Method: Step 3 & 4 in Algorithm 3.5.6 of Sturmfels' Algorithmic Invariant Theory
      atomicExt := select(L, ll-> (#ll =!= d+1));
      scan(subsets(#atomicExt,2), a -> (
		E := sort toList atomicExt#(a#0);
		F := sort toList atomicExt#(a#1);
		if(#E + #F > d+1) then (
		     newOrder := inversePermutation(sort(E) | sort(F) | sort toList(set(0..n) - (E|F))); 
		     PermP := permutePoints(P, d,n, newOrder); -- permute the indices so that E and F comes first
		     if(o.OnlineStraightening) then (PermP = straightenPoly(PermP,d,n););
		     found := 1;
		     scan(terms PermP, monomial -> (
			  supp := (support(monomial))_{0,1};
			  firstRow := set (baseName(supp#0))#1; --first row of tableau
			  secondRow := set (baseName(supp#1))#1; -- second row of tableau
			  if((not isSubset(set(0..#E-1),firstRow)) or (not isSubset(set(0..#F-1), firstRow+secondRow)) or (not isSubset(firstRow, set(0..#E+#F-1) ))) then (
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
			  Psub := 0;
			  if(o.OnlineStraightening) then (
			       Psub = straightenPoly(permutePoints(sub(PermP, substitutions), d, n, inverseNewOrder),d,n);
			       ) else (
			       Psub = permutePoints(sub(PermP, substitutions), d, n, inverseNewOrder);
			       );
		     	  break({{E,F}, Psub , sort apply(toList(0..(#E + #F - d -2)), i -> inverseNewOrder_i)});    
		     )
	  	)
      )
  )
)


  
   -------------------- Auxiliary functions ---------------------------------


  permutePoints =  (P, d, n, sigma) -> (
   	-- INPUT:  P is a polynomial in coordinate ring of Grassmannian(d,n), sigma as above
	-- OUTPUT:  another polynomial in same variables, after substitution
	-- This one does substitutions only for the variables appearing in the polynomial P
      if(isConstant P) then (return P);
      sub(P, apply(unique flatten ((terms P) / support), v -> (
			     v => indicesToRingElement(ring P, d,n, apply(toList (baseName v)#1, i -> sigma#i))--uses straightening when it returns a ring element
     	       	    	       )
      			  )
       )
  )

{* useless?
  permutePoints :=  (R,d, n, sigma) -> (
       -- INPUT: R is coordinate ring of Grassmannian(d,n)
       --     	 sigma is a list of length of n, containing elements from {0,..,d}, with repetition allowed
       -- OUTPUT: list of "permuted variable"s, can be used to make a ring map
       apply(flatten entries vars R, v -> (
     	     indicesToRingElement(R, d,n, apply(toList (baseName v)#1, i -> sigma#i))
	 ) 
	 )
       )
  }
*}

 ------------------------------------------------------------------- 

  indicesToRingElement = (R, d, n, indexList) -> (
      -- INPUT:  R is the ring of Grassmannian(d,n), 
      --         indexList is a list or sequence of indices between 0 and n
      --     	  The list gets sorted and appropriate sign is assigned
      --     	  If there are repeated indices, 0 is assigned
      -- OUTPUT: the Plucker variable with indices indexList
    	   if(#(set indexList) == #indexList) then (
       	    	 sign indexList * sub(value ((baseName R_0)#0)_(toSequence(sort indexList)), R)
	    ) else (
	    	 sub(0, R)
    		 )
 )
  
   ------------------------------------------------------------------- 

  sign = sigma ->(
       -- Sign of a permutation
       -- 0 if sigma contains repeated elements
       product apply(subsets(#sigma,2), l -> (
		 if(sigma#(l#0) > sigma#(l#1)) then (-1 )
		 else if(sigma#(l#0) < sigma#(l#1) ) then (1)
		 else (0)
		 )
	    )
       )


--------------------Straightening without a full Groebner basis--------
----------signAndShuffle, signOfShuffle copied from schubert.m2 written by Sturmfels and Yu
----------straightenPoly is modified code from the same file

signAndShuffle = (a,b) -> (
     ct := 0;
     i := 0; m := #a;
     j := 0; n := #b;
     sh := while a#?i or b#?j list (
	  t := if a#?i then a#i;
	  u := if b#?j then b#j;
     	  if t === u then return (0,());
	  if t === null then (j = j+1; u)
	  else if u === null or t < u then (i = i+1; t)
     	  else (ct = ct + m-i; j = j+1; u));
     ((-1)^ct, toSequence sh));

signOfShuffle = (a,b) -> (
     ct := 0;
     i := 0; m := #a;
     j := 0; n := #b;
     while i<m and j<n do (
     	  if a#i == b#j then return 0;
     	  if a#i < b#j then i = i+1
     	  else (ct = ct + m-i; j = j+1));
     (-1)^ct);

straightenQuick = (P,d,n) ->(
     if(isConstant P) then (return(P););
     p :=(baseName(first support(first terms P)))#0;
     I := sub(Grassmannian(d,n, Variable => p), ring P);
     return(P % I);     
     )

straightenPoly= method();
straightenPoly(RingElement,ZZ,ZZ) := (P,d,n) ->(

     R:= ring P;
     L:= terms P;
     
     --list containing {coefficient, support} for each term
     tableauxList :=apply(L, i-> (coefficient((entries monomials i)#0#0,i), sort apply(support i, j-> (baseName j)#1)));
     --look for a nonstandard tableaux
     nonStandard:=null;
     t:=0;
     --exit when nonstandard = position of the first inversion and the rows in which it occurs
     for i from 0 to (#tableauxList-1) when nonStandard === null do(
	  nonStandard = findNonstandardTerm((tableauxList#i)#1);
	  --t equals the index of the nonstandard tableax in tableauxlist
	  t=i;
	  );
     if nonStandard === null then return P
     else (
	  up:= (nonStandard#0);
	  r:= (nonStandard#1)#0;
	  s:=(nonStandard#1)#1;
	  snake := s_{0..up} | r_{up..d};
     	  pluckerSyz:=sum for s1 in subsets(snake,up+1) list (
	       s2 := snake - set s1;
	       (sgn1,a) := signAndShuffle(r_{0..up-1}, s2); 
	       if sgn1 == 0 then continue;
	       (sgn2,b) := signAndShuffle(s1, s_{up+1..d});
	       if sgn2 == 0 then continue;
	       sgn := sgn1 * sgn2 * signOfShuffle(s1,s2);
	       sgn *R_(((baseName R_0)#0)_a) *R_(((baseName R_0)#0)_b));
     );
   newP:=P - (tableauxList#t)#0*pluckerSyz*product( apply(toList( set((tableauxList#t)#1) -set{r,s}), i->R_(((baseName R_0)#0)_i) ));
   straightenPoly(newP,d,n)
 )
 
findNonstandardTerm = T ->(
      --T = tableaux = list of sequences
      --returns position of inversion and the rows where the inversion took place
      up:=null;
      pair:=null;
      P :=subsets(T,2);
      for i from 0 to (#P-1) do(
	   up = position(((P#i)#0), ((P#i)#1), (a,b) -> a>b);
	   if up =!=null then( 
		pair = P#i;
		return (up, pair);
		);
      );
return null;
 )



 ------------------------------------------------------------------- 
  ----------------------Documentation--------------------------------
   ------------------------------------------------------------------- 

beginDocumentation()

doc ///
  Key
       CayleyFactorization
  Headline
       Cayley Factorization
  Description
   Text
   	This is a package that can be used to factor multilinear bracket polynomials as simple expressions in the Grassmann-Cayley algebra.  We used Neil White's algorithm, as described in the book "Algorithms in Invariant Theory" by Bernd Sturmfels.
///

doc ///
  Key
       cayleyFactor
       (cayleyFactor, RingElement, ZZ, ZZ)
       (cayleyFactor, RingElement, ZZ, ZZ, List)
  Headline
       Factors a multilinear bracket polynomial as a simple expression in the Grassmann-Cayley algebra
  Usage
       C = cayleyFactor(P,d,n)
       C = cayleyFactor(P,d,n,partialAtoms)
       
  Inputs
     P: RingElement
           a multilinear polynomial in the coordinate ring of Grassmannian(d,n)
     d: ZZ
     n: ZZ
     partialAtoms:List 
                 an optional list containing disjoint sets of points known to be in the same equivalence class
  Outputs
     C: Expression
     	  \{,\} denotes join, and (,) denotes meet
  Consequences

  Description
   Text
   Text
   Example
   	d = 2; n=5;
	Grassmannian(d,n);
	use((ring oo) / oo);
  	P = p_(1,2,5)*p_(0,3,4)+ p_(1,2,3)*p_(0,4,5)-p_(1,3,5)*p_(0,2,4);
	cayleyFactor(P,d,n)
   Text
   Example
  Caveat
       We do not check if the input polynomial is multilinear.  We assume that the input polynomial P is already in the coordinate ring of the Grassmannian.
  SeeAlso
///

 ------------------------------------------------------------------- 

TEST ///

d=2; n=5;
R = ZZ[apply(subsets(0..n,d+1), a -> p_(toSequence(a)))];
P = p_(1,2,5)*p_(0,3,4)+ p_(1,2,3)*p_(0,4,5)-p_(1,3,5)*p_(0,2,4);
time cayleyFactor(P,d,n, OnlineStraightening => true)
I = Grassmannian(d,n);
S = ring(I) / I;
time cayleyFactor(P,d,n, OnlineStraightening => false)

///

 ------------------------------------------------------------------- 


---- Josephine's tests
end

restart
uninstallPackage("CayleyFactorization")
installPackage("CayleyFactorization", RemakeAllDocumentation => true )
debug loadPackage "CayleyFactorization"

d=2;n=5;
S = ring( Grassmannian(d,n))
S = ZZ[apply(subsets(0..n,d+1), a -> p_(toSequence(a)))]

P = p_(0,3,4)*p_(1,2,5)


straightenPoly(P,d,n)
straightenQuick(P,d,n)

R = GrassmannCayleyAlgebra(2,5)
use R
meet(a_1*a_2+a_3, a_3*a_4+a_5)
     
viewHelp CayleyFactorization
d = 2; n=5;
I = Grassmannian(d,n);
R = ring oo;
P = p_(1,2,5)*p_(0,3,4)+ p_(1,2,3)*p_(0,4,5)-p_(1,3,5)*p_(0,2,4); -- factorable
time cayleyFactor(P,d,n, OnlineStraightening => true)

R = R / I;
time cayleyFactor(P,d,n, OnlineStraightening => false)

permutePoints(P, d, n, {5,4,3,2,1,0})

L = toList listAtoms(P, d, n, OnlineStraightening => true)
factorBrackets(P,d,n,L,OnlineStraightening => true)

d=2; n=5;
Grassmannian(d,n);
R = (ring oo) / oo;
E = ZZ[a_0..a_n,e_0..e_d, SkewCommutative => true]
GC = E ** R
I = ideal apply(a_0..a_n, a-> a* product(toList(e_0..e_d))) + ideal apply(subsets(0..n,d+1),s-> p_(toSequence(sort toList s))*product(toList(e_0..e_d)) - product apply(s, i-> a_i))
GC1 = GC / I;

A = 2*p_(0,1,2)*a_3*a_4
B = a_1*a_2 - a_0*a_4

meet(a_0*a_1, a_3*a_4,d,n)*meet(a_1*a_2, a_4*a_5,d,n)*meet(a_2*a_3, a_5*a_0,d,n)

meet( meet( a_0*a_1, a_2*a_3, d,n) , a_4*a_5, d, n)
use R
cayleyFactor( p_(0,1,3)*p_(2,4,5)-p_(0,1,2)*p_(3,4,5), d,n)

eliminate(apply(gens R, v -> promote(v,GC1)), x_1*x_3*x_2)

 
l = {1,2,5}
n=5;
d=2;
L = {{0,1,2},{1,3},{3,4,5},{0,1,4,5},{1,3,5}};
L = {{0,1,2},{1,3},{3,4,5},{0,1,4,5}};
L = subsets(n+1,d-1)| subsets(n+1,d) | {{0,1,2},{3,4,5}}
factorBrackets(P, d, n, L)
E = {0,2}; F = {1,4};

d=2;n=6;
Grassmannian(d,n);
use((ring oo) / oo);
P = p_(0,1,4)*p_(2,3,5) - p_(1,3,4)*p_(0,2,5);
cayleyFactor(P,d,n)

012345
abcdef

d=2;n=8;
I = Grassmannian(d,n);
R = ring I;
S = R/I;
use(S)
use((ring oo) / oo);
partialAtoms = toList apply(0..n, i->set {i})
P = p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8);
time cayleyFactor(P,d,n)
time cayleyFactor(P,d,n, OnlineStraightening => false)

L = toList listAtoms(P, d, n, OnlineStraightening => true)
L = toList listAtoms(P, d, n, OnlineStraightening => false)
L = {set {0, 1}, set {2, 3}, set {8, 7}, set {4}, set {5, 6}}
findPairFactor(P,d,n,L,OnlineStraightening => true)

P = p_(0,2,4)*p_(1,3,5)-2*p_(0,1,4)*p_(2,3,5)-p_(0,2,3)*p_(1,4,5)+p_(0,1,3)*p_(2,4,5)-2*p_(0,1,2)*p_(3,4,5)+2*p_(0,1,2);
partialAtoms = {set {7}, set {6}, set {8}, set {1, 2}, set {0}};

d=3;n=7;
Grassmannian(d,n);
use((ring oo) / oo);
P = p_(0,3,4,5)*p_(1,2,6,7) - p_(1,3,4,5)*p_(0,2,6,7) +p_(2,3,4,5)*p_(0,1,6,7);


L=listAtoms(P, 2, 5);
L = apply((toList L),a->toList a)
L = reverse L
factorBrackets(P,d,n,toList L) 
findPairFactor(P,d,n,toList L)
sigma = {2,3,0,1,5,7,6,8,4}



------ Jessica's tests

end
restart
uninstallPackage "CayleyFactorization"
debug loadPackage "CayleyFactorization"
d = 2;
n=8;
I = Grassmannian(d,n),;
use ring I/I;
P = p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,6)*p_(2,3,4)*p_(5,7,8)
F = cayleyFactor(P,d,n);
peek F

use ring I;

restart
debug loadPackage "CayleyFactorization"
d=2;n=8;
I = Grassmannian(d,n),;
R = ring I;
use R;
P = p_(0,1,5)*p_(2,3,4)
P = p_(0,1,5)*p_(2,3,4)*p_(6,7,8)

P = straightenPoly(P,d,n)

 straightenPoly(p_(0,1,2)*p_(3,4,5),d,n)

S =R/I;
p_(0,1,5)*p_(2,3,4)

use S;

d = 6;
n=12;
I = Grassmannian(d,n),;


use((ring oo)/ oo);
P = p_(0,1,4)*p_(2,3,5)-p_(1,3,4)*p_(0,2,5);
F = cayleyFactor(P, 2,5)
peek F
L = listAtoms(p_(0,1,2)*p_(3,4,5)+p_(0,1,3)*p_(2,4,5),2,5)

R = ring Grassmannian(2,8);
use((ring oo)/ oo);
P = (p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8);
d=2;
n=8;


F= cayleyFactor(P, 2,8)
L=listAtoms(p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8), 2, 8)
toList L

K = listAtoms(p_(0,4,5)*p_(6,7,8)-p_(0,4,6)*p_(5,7,8), {set {0}, set {7, 8}, set {4}, set {5, 6}}, 2, 8)

toList K     
isAtom(0,4, p_(0,4,5)*p_(6,7,8)-p_(0,4,6)*p_(5,7,8),2,8)

isAtom(2,3,p_(0,1,2)*p_(3,4,5)*p_(6,7,8)-p_(0,1,2)*p_(3,4,6)*p_(5,7,8)-p_(0,1,3)*p_(2,4,5)*p_(6,7,8)+p_(0,1,3)*p_(2,4,6)*p_(5,7,8), 2, 8)

isAtom(4,5,p_(0,1,2)*p_(3,4,5)+p_(0,1,3)*p_(2,4,5),2,5)

L =isAtom(0,0,p_(1,2,3)*p_(2,3,4),2,4)


