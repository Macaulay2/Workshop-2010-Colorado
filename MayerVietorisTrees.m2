-- -*- coding: utf-8 -*-
newPackage(
        "MayerVietorisTrees",
        Version => "0.1", 
        Date => "August 8, 2010",
        Authors => {{Name => "Eduardo Saenz-de-Cabezon"},
	     	    {Name => "Courtney Gibbons"},
		    {Name => "Dennis Moore"}},
	--CurrentDevelopers => {{Name => "Eduardo"},
	--    	                {Name => "Courtney"},
	--     	    	      	{Name => "Dennis"}};
	--PastDevelopers => { };
	--Contributors => { };
	--Acknowledgments => { };
        Headline => "A package for computing Betti numbers and bounds on homological invariants for monomial ideals",
        DebuggingMode => true
        )

export {fullMVT, relMVT, relevantNodes, relNodesGens, refineUndecided, splitNodes,
     projDimMVT, regMVT, lowerBettiMVT, upperBettiMVT, pseudoBettiMVT, PivotStrategy, 
     hilbertSeriesMVT}

--TO DO:
-- v0: document methods
-- v0: create relMVT
-- v0: change output for all things to (monomial, dimension, position)
--
-- Before Version 1:
-- v1: document methods well
-- v1: consistency among output, naming conventions (in our program, in M2)
-- v1: data types? 
--     --MVTs as hash tables
-- v1: print MVTs, pseudoBettiMVTs nicely
--     --output MVT as tree in M2
--     --output for LaTeX
--     --output pseudoBettiMVTs like betti diagrams
-- v1: get MVT C code added to the engine
-- v1: coarse hilbertSeriesMVT (total degrees)
-- v1: hilbertFunctionMVT with output that mirrors the method hilbertFunction(ZZ,Type)
-- 
-- Before Version 2:
-- v2: specializations of the code
--     --obtain the n-1 betti multidegrees for getting the irreducible composition
--     --euler characteristic of the simplicial complex
--
-- Before later versions
-- vN: Mapping cone resolution (MCR) with differentials <-- nice to have the M2 code for small examples
-- vN: C version of MCR for the engine <-- for larger computations

-- vInfinity: refine method that refines *everything* (gives minimal free res --> open problem)


 ----------------------------
-- Internal Support Methods --
 ----------------------------

pivot = method(Options => {PivotStrategy => 1});  --Chooses the pivot generator for creating a MVT from a monomial ideal
pivot(Matrix) := o -> (I) -> {
     if o.PivotStrategy == 1 then {
     	  return first first entries I;
	  }
     else {
	  if o.PivotStrategy == 2 then {
	       return last first entries I;
	       }
	  else error "You have not picked a valid strategy"
	  }
     }

idealRight = method(Options => {PivotStrategy => 1});  --Creates the right child of node in an MVT
idealRight(Matrix) := o -> (I) -> {
     return gens (monomialIdeal I - monomialIdeal pivot(I,PivotStrategy => o.PivotStrategy));
     }

idealLeft = method(Options => {PivotStrategy => 1});   --Creates the left child of a node in an MVT
idealLeft(Matrix) := o -> (I) -> {
     return gens intersect(monomialIdeal idealRight(I,PivotStrategy => o.PivotStrategy), monomialIdeal pivot(I,PivotStrategy => o.PivotStrategy));
      -- this can be optimized (we're computing pivot 2x)
     }

myFullMVT = method(Options => {PivotStrategy => 1});   --Creates a full MVT (all nodes, not just relevant ones)
myFullMVT(Matrix,ZZ,ZZ) := o -> (M,myDim,myPos) -> {
     undone := {};
     undone = undone | {(M,0,1)};
     L := {(M,0,1)};
     while undone != {} do { A := undone#0;
	  undone = remove(undone,0);
	  J := A#0;
	  if numcols J > 1 then {
	       L1 := idealLeft(J,PivotStrategy => o.PivotStrategy);
	       L2 := idealRight(J,PivotStrategy => o.PivotStrategy);
	       L = L | {(L1,1+A#1,2*A#2)}; --relevant nodes
	       L = L | {(L2,A#1,1+2*A#2)}; --irrelevant nodes
	       if numcols L1 != 1 then {	       
		    if numcols L1 == 2 then { 
			 L11 := idealLeft(L1,PivotStrategy => o.PivotStrategy);
			 L12 := idealRight(L1,PivotStrategy => o.PivotStrategy);
			 L = L | {(L11,2+A#1,4*A#2)} | {(L12,1+A#1,1+4*A#2)};
			 }
	       	    else  {undone = undone | {(L1,1+A#1,2*A#2)}};
		    };
	       if numcols L2 != 1 then {
	       	    if numcols L2 == 2 then { 
			 L21 := idealLeft(L2,PivotStrategy => o.PivotStrategy);
			 L22 := idealRight(L2,PivotStrategy => o.PivotStrategy);
			 L = L | {(L21,1+A#1,2+4*A#2)} | {(L22,A#1,3+4*A#2)};
		    	 }
		    else {undone = undone | {(L2,A#1,1+2*A#2)}};
		    }
	  }
     }; -- \ends the "do"
     return L;
     }

myRelMVT = method(Options => {PivotStrategy => 1});    --Creates a list of only the relevant nodes in an MVT
myRelMVT(Matrix,ZZ,ZZ) := o -> (M,myDim,myPos) -> {
     undone := {};
     undone = undone | {(M,0,1)};
     L := {(M,0,1)};
     while undone != {} do { A := undone#0;
	  undone = remove(undone,0);
	  J := A#0;
	  if numcols J > 1 then {
	       L1 := idealLeft(J,PivotStrategy => o.PivotStrategy);
	       L2 := idealRight(J,PivotStrategy => o.PivotStrategy);
	       L = L | {(L1,1+A#1,2*A#2)}; --relevant nodes
	       --L = L | {(L2,A#1,1+2*A#2)}; --irrelevant nodes; not output
	       if numcols L1 != 1 then {	       
		    if numcols L1 == 2 then { 
			 L11 := idealLeft(L1,PivotStrategy => o.PivotStrategy);
			 L12 := idealRight(L1,PivotStrategy => o.PivotStrategy);
			 L = L | {(L11,2+A#1,4*A#2)};
			 }
	       	    else  {undone = undone | {(L1,1+A#1,2*A#2)}};
		    };
	       if numcols L2 != 1 then {
	       	    if numcols L2 == 2 then { 
			 L21 := idealLeft(L2,PivotStrategy => o.PivotStrategy);
			 L22 := idealRight(L2,PivotStrategy => o.PivotStrategy);
			 L = L | {(L21,1+A#1,2+4*A#2)};
		    	 }
		    else {undone = undone | {(L2,A#1,1+2*A#2)}};
		    }
	  }
     }; -- \ends the "do"
     return L;
     }

relNodesGens = method();	    	 
relNodesGens(List) := L -> {
     return sort flatten for i from 0 to length(L)-1 list 
     for j from 0 to numcols (L#i#0)-1 list (entries L#i#0_j,L#i#1,L#i#2); --(monomial,dimension,position)
     }

refineUndecided = method(TypicalValue=> List);
refineUndecided(List,List):= (Und,Dec)-> {
    M:=apply(Und, i->{i#1,i#2});
    T:= new MutableHashTable from apply(Und,i->{i#0,{}});
    for i from 0 to #Und-1 do T#(Und#i#0)= append(T#(Und#i#0),Und#i#1);    
    W:=new HashTable from T;
    Y:=new MutableHashTable from applyValues(W, tally);
    L:=#(keys Y);
    for i from 0 to L-1 do
    {
      if (#Y#((keys Y)#i)==1) then 
        {
         dec=positions(Und,k->first k == (keys Y)#i);   --last parenthesis was omitted!
         Dec=append(Dec,take(Und,{first dec, last dec}));
         Und=drop(Und,{first dec, last dec});
        }
      else null;
    };
    return {Und, flatten Dec}
};

splitNodes = method();  --returns a list of "good" and "bad" generators that affect homological invariants
splitNodes(List) := (myList) -> {
   myTally := tally apply(myList, i -> i#0);
   uniqueList := apply(select(pairs myTally, p -> p#1 == 1), first);
   nonUniqueList  := apply(select(pairs myTally, p -> p#1 > 1), first);
   nonRepList := select(myList, p -> member(p#0,uniqueList));
   repList := select(myList, p -> member(p#0,nonUniqueList));
   return {nonRepList,repList};
   }

maxDim = method(); 
maxDim(List) := L -> {
     l = length L - 1;
     if L != {} then
     return max (for i from 0 to l list L#i#1)
     else return 0;
     }

maxReg = method();
maxReg(List) := L -> {
     l = length L - 1;
     if L != {} then
     return max (for i from 0 to l list ((first degree first (L#i#0)) - L#i#1)) --total degree of monomial - L#i#1
     else return 0;
     }

pseudoBettiHelper = method();  -- returns a visual tally and a mutable hash table that mimic the information found in a Betti tally and the total betti numbers (but this method returns bounds on Betti numbers)
pseudoBettiHelper(BettiTally,BettiTally) := (lowBetti,highBetti) -> {
	P := new List from sort (pairs (lowBetti) | pairs (highBetti));
	P = unique P;
	myTally = tally apply(P, i -> i#0);
	--to start, check if first entries of the hash table are the same
	--uniqueList := unique P;
        hasBoundsList := apply(select(pairs myTally, p -> p#1 > 1), first);
	fullBoundsList := select(P, p -> member(p#0,hasBoundsList));
   	boundsAgreeList := select(P, p -> not (member(p#0,hasBoundsList)));
	agreeList := for i from 0 to (#boundsAgreeList-1) list (boundsAgreeList#i#0,{boundsAgreeList#i#1,boundsAgreeList#i#1}); 
	printAgreeList := apply(agreeList,p -> (p#0,p#1#0));
	disagreeList := for i from 0 to floor ((#fullBoundsList-1)/2) list (fullBoundsList#(2*i)#0,{fullBoundsList#(2*i)#1,fullBoundsList#(2*i+1)#1});
	entireList := sort(agreeList | disagreeList);
	printEntireList := sort(printAgreeList | disagreeList);
	--grabbing the total bettis (summing up the bounds)
	totals := new MutableHashTable;
	V := new MutableHashTable;
	homDegList := unique apply(entireList, p -> p#0#0);
	for i from 0 to #homDegList-1 do {
     	     V#i = select(entireList, p -> p#0#0 == homDegList#i);
     	     };
	for i from 0 to #V-1 do {
     	     listVi = new List from V#i;
      	     helperList= {};
     	     for j from 0 to #listVi-1 do {
	  	  helperList = helperList | {last listVi#j};
	  	  totals#(homDegList#i) = sum(helperList);
	  	  };
	     };
	for i from 0 to #homDegList-1 do {
	     if totals#(homDegList#i)#0 == totals#(homDegList#i)#1 then {
		  totals#(homDegList#i) = totals#(homDegList#i)#0
		  };
	     };
 	outPut = {tally printEntireList, peek totals}
	}




 ----------------------
-- Methods for Export --
 ----------------------

fullMVT = method(Options => {PivotStrategy => 1} );
fullMVT(MonomialIdeal) := o -> (I) -> {
     J := gens I;
     T := myFullMVT(J,1,0, PivotStrategy => o.PivotStrategy);
     return T;
     }
  
relMVT = method(Options => {PivotStrategy => 1} );
relMVT(MonomialIdeal) := o -> (I) -> {
     J := gens I;
     T := myRelMVT(J,1,0, PivotStrategy => o.PivotStrategy);
     return T;
     }

relevantNodes = method(); --input a MVT as a list of sequences, output the sequences with 1 or even first position
relevantNodes(List) := (L) -> {
     --code to check that the input looks like a MVT {}
     
     --code that gives nodes:
     l := length L - 1;
     K := {L#0};
     for i from 0 to l do {
	  if even L#i#0 then { K = K | {L#i} };
	  };
     return K;
     }

projDimMVT = method(Options => {PivotStrategy => 1});
projDimMVT(MonomialIdeal) := o -> (I) -> {
     myNodes := relNodesGens(relMVT(I,PivotStrategy => o.PivotStrategy));
     nonRep := first splitNodes(myNodes);
     rep := last splitNodes(myNodes);
     if maxDim(nonRep) >= maxDim(rep) then return maxDim(nonRep)
     else return (maxDim(nonRep),maxDim(rep));
     }

regMVT = method(Options => {PivotStrategy => 1});
regMVT(MonomialIdeal) := o -> (I) -> {
     myNodes := relNodesGens(relMVT(I,PivotStrategy => o.PivotStrategy));
     nonRep := first splitNodes(myNodes);
     rep := last splitNodes(myNodes);
     if maxReg(nonRep) >= maxReg(rep) then return maxReg(nonRep)
     else return (maxReg(nonRep),maxReg(rep));
     }

lowerBettiMVT = method(Options => {PivotStrategy => 1}); --returns lower bounds on the Betti numbers of a monomial ideal I
lowerBettiMVT(MonomialIdeal) := o -> I -> {
     S := splitNodes relNodesGens relMVT(I,PivotStrategy => o.PivotStrategy);
     L := (refineUndecided(S#1,S#0))#1;
     M := apply(L, i->{i#1,i#0});
     T := new MutableHashTable from apply(L,i->{i#1,{}});
     for i from 0 to #M-1 do T#(M#i#0)= append(T#(M#i#0),first degree first(M#i#1));
     W := new HashTable from T;
     Y := applyValues (W, tally);
     B :={};
     for i from 0 to #Y-1 do {
     	  for j from 0 to #(Y#((keys Y)#i))-1 do B = append(B,((keys Y)#i,{(keys Y#((keys Y)#i))#j},(keys Y#((keys Y)#i))#j)=>(Y#((keys Y)#i))#((keys Y#((keys Y)#i))#j))
	  };
     t := new BettiTally from B;
     return t
     }

undecidedBettiMVT = method(Options => {PivotStrategy => 1}); --returns upper bounds on the Betti numbers of a monomial ideal I
undecidedBettiMVT(MonomialIdeal) := o -> I -> {
     S := splitNodes relNodesGens relMVT(I,PivotStrategy => o.PivotStrategy);
     L := (refineUndecided(S#1,S#0))#0;
     M := apply(L, i->{i#1,i#0});
     T := new MutableHashTable from apply(L,i->{i#1,{}});
     for i from 0 to #M-1 do T#(M#i#0)= append(T#(M#i#0),first degree first(M#i#1));
     W := new HashTable from T;
     Y := applyValues (W, tally);
     B :={};
     for i from 0 to #Y-1 do {
     	  for j from 0 to #(Y#((keys Y)#i))-1 do B = append(B,((keys Y)#i,{(keys Y#((keys Y)#i))#j},(keys Y#((keys Y)#i))#j)=>(Y#((keys Y)#i))#((keys Y#((keys Y)#i))#j))
	  };
     t := new BettiTally from B;
     return t
     }

upperBettiMVT = method(Options => {PivotStrategy => 1});
upperBettiMVT(MonomialIdeal) := o -> I -> {
     t := lowerBettiMVT(I,PivotStrategy => o.PivotStrategy) ++ undecidedBettiMVT(I,PivotStrategy => o.PivotStrategy);
     return t
     }

pseudoBettiMVT = method(Options => {PivotStrategy => 1}); -- outputs a VirtualTally similar to a BettiTally that gives bounds on the dimension
pseudoBettiMVT(MonomialIdeal) := o -> I -> {
     LB := lowerBettiMVT(I, PivotStrategy => o.PivotStrategy);
     UB := upperBettiMVT(I, PivotStrategy => o.PivotStrategy);
     P := pseudoBettiHelper(LB,UB);
     return P
     }

hilbertSeriesMVT = method(TypicalValue => RingElement, Options => {PivotStrategy => 1}); --returns the numerator of the multigraded Hilbert series of an ideal I
hilbertSeriesMVT(MonomialIdeal) := o -> I -> {
     L:=relMVT(I,PivotStrategy => o.PivotStrategy);
     L1:=apply(#L,i->{first entries L#i#0,L#i#1});
     Numerator:=sub(0,ring first first first L1);
     for i from 0 to #L1-1 do Numerator=Numerator+sum(L1#i#0)*(-1)^(L1#i#1);
     return Numerator
};    --should the output be a fraction of class 'divide' instead of just the numerator?



 -----------------
-- Documentation --
 -----------------

beginDocumentation()

document { 
     Key => MayerVietorisTrees,
     Headline => "Computes bounds on homological invariants for monomial ideals.",
     "This package can output full MVTs or MVTs containing only the relevant nodes.",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal(x^2,y^2,x*y)",
          "fullMVT I",
	  "relMVT I",
	  "projDimMVT I",
	  "regMVT I",
	  "upperBettiMVT I",
	  "lowerBettiMVT I",
	  "pseudoBettiMVT I",
          },
     "The user may specify a strategy for choosing the pivot generators in these MVT computations.",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal(x^2,y^2,x*y)",
          "relMVT I",
	  "relMVT (I,PivotStrategy => 2)",
          },
     "If the user has input an MVT, the method " TO relevantNodes " outputs only the relevant nodes of the tree.",
     Caveat => {"This package is most useful for computing small examples."},
     Subnodes => {
          TO fullMVT,
          TO relMVT,
	  TO relevantNodes,
	  TO projDimMVT,
	  TO regMVT,
	  TO lowerBettiMVT,
	  TO upperBettiMVT,
	  TO pseudoBettiMVT,
	  TO PivotStrategy
          }
     }
     
document {
     Key => {fullMVT,(fullMVT,MonomialIdeal)},
     Headline => "Outputs a Mayer-Vietoris Tree from a monomial ideal. ",
     Usage => T = fullMVT(I),
     Inputs => {
	  MonomialIdeal
          -- each input is a hypertext list
          },
     Outputs => {
          List
	  -- each output is a hypertext list
          },
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "fullMVT (I,PivotStrategy => 2)"
          },
     Caveat => {"This method is inefficient for computing large examples."}
     }

document {
     Key => [fullMVT, PivotStrategy],
     Usage => "fullMVT(...,PivotStrategy => n)",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "fullMVT (I,PivotStrategy => 2)"
          },
     }

document {
     Key => {relMVT, (relMVT,MonomialIdeal)},
     Headline => "Outputs the relevant nodes of a Mayer-Vietoris tree from a monomial ideal.",
     Usage => "relMVT(I)",
     Inputs => {
	  I:MonomialIdeal,
          -- each input is a hypertext list
          },
     Outputs => {
          T:List
	  -- each output is a hypertext list
          },
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "relMVT (I,PivotStrategy => 2)"
          },
     Caveat => {"This method is inefficient for computing large examples."}
     }

document {
     Key => [relMVT, PivotStrategy],
     Usage => "relMVT(...,PivotStrategy => n) ",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "relMVT (I,PivotStrategy => 2)"
          },
     }

document {
     Key => {relevantNodes, (relevantNodes,List)},
     Headline => "Outputs the relevant nodes of any list in the form of a Mayer Vietoris tree. ",
     Usage => "relevantNodes(L)",
     Inputs => {
	  L:List, " of the form of an MVT.",
          -- each input is a hypertext list
          },
     Outputs => {
          T:List
	  -- each output is a hypertext list
          },
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "relMVT I",
	  "relevantNodes oo"
          },
     Caveat => {"This method only understands lists that appear as those output by ", TO fullMVT, " or ", TO relMVT, " ."}
     }
   
   
document {
     Key => PivotStrategy,
     Headline => "An option to specify how pivot generators are chosen.",
     "The default option is 1 .",
     "PivotStrategy => 1 chooses the largest generator with respect to ambient monomial ordering for the ring. ",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal(x^2,y^2,x*y)",
          "fullMVT(I,PivotStrategy => 1)"
          },
     "PivotStrategy => 2 chooses the smallest generator with respect to the ambient monomial ordering for the ring. ",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal(x^2,y^2,x*y)",
          "fullMVT(I,PivotStrategy => 2)"
          },
     Caveat => {"Only two strategies are currently implemented."}
     }

document {
     Key => {hilbertSeriesMVT,(hilbertSeriesMVT,MonomialIdeal)},
     Headline => "computes the numerator of the Hilbert series",
     Usage => "hilbertSeriesMVT I",
     Inputs => {
          MonomialIdeal
          },
     Outputs => {
          RingElement
          },
     "The Hilbert series is a formal power series whose coefficients are the dimensions of the corresponding graded component. Note that the numerator is provided as a polynomial in the variables of the ring.",
     EXAMPLE {
          "R=QQ[x,y]",
          "I=monomialIdeal(x^2,y^2,x*y)",
          "hilbertSeriesMVT I"
          },
 --    "There can be explanatory prose here in the form of a hypertext list.",
     Caveat => {"Only the numerator of the Hilbert series is returned. The numerator is not reduced."}
     }

document {
     Key => {projDimMVT,(projDimMVT,MonomialIdeal)},
     Headline => "computes bounds for the projective dimension ",
     Usage => "projDimMVT I",
     Inputs => {
          MonomialIdeal
          },
     Outputs => {
          ZZ or {ZZ,ZZ}
          },
     "Bounds for the projective dimension are computed using both nonrepeated nodes and repeated nodes.  If the values agree, this value is returned.  Otherwise both values are returned in a list.",
     EXAMPLE {
          "R=QQ[x,y]",
          "I=monomialIdeal(x^2,y^2,x*y)",
          "projDimMVT I"
          }
 --    "There can be explanatory prose here in the form of a hypertext list.",
 --    Caveat => {"warning"},
     SeeAlso => {"regMVT"},
     }

document {
     Key => [projDimMVT, PivotStrategy],
     Usage => "projDimMVT(...,PivotStrategy => n)",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "projDimMVT (I,PivotStrategy => 2)"
          },
     }

document {
     Key => {regMVT,(regMVT,MonomialIdeal)},
     Headline => "computes the regularity",
     Usage => "regMVT I",
     Inputs => {
          MonomialIdeal
          },
     Outputs => {
          ZZ or {ZZ,ZZ}
          },
     "Bounds for the regularity are computed using both nonrepeated nodes and repeated nodes.  If the values agree, this value is returned.  Otherwise both values are returned in a list.",
     EXAMPLE {
          "R=QQ[x,y]",
          "I=monomialIdeal(x^2,y^2,x*y)",
          "regMVT I"
          }
 --    "There can be explanatory prose here in the form of a hypertext list.",
 --    Caveat => {"warning"},
     SeeAlso => {"projDimMVT"},
     }

document {
     Key => [regMVT, PivotStrategy],
     Usage => "regMVT(...,PivotStrategy => n)",
     EXAMPLE {
          "R = QQ[x,y,z]",
          "I = monomialIdeal (x^2,y^2,x*y)",
          "regMVT (I,PivotStrategy => 2)"
          },
     }

document {
     Key => lowerBettiMVT,
     Headline=>"Outputs lower bounds for the Betti numbers of a monomial ideal, based on a Mayer-Vietoris tree of it."
}


document {
     Key => (lowerBettiMVT,MonomialIdeal),
     Headline=>"Outputs lower bounds for the Betti numbers of a monomial ideal, based on a Mayer-Vietoris tree of it."
     Usage => "lowerBettiMVT(I)",
     Inputs => {
          MonomialIdeal
          -- each input is a hypertext list
          },
     Outputs => {
          "A Betti diagram"
          -- each output is a hypertext list
          },
     EXAMPLE {
          "R=QQ[x,y,z]",
          "I = monomialIdeal(x^2,y^2,x*y)",
          "lowerBettiMVT(I)"
          },
     }

document {
     Key => [upperBettiMVT, PivotStrategy]
     Headline=>"The Pivot Strategy is the one that will be used for the computation of the Mayer-Vietoris tree."
}

document {
     Key => upperBettiMVT,
     Headline=>"Outputs lower bounds for the Betti numbers of a monomial ideal, based on a Mayer-Vietoris tree of it."
}


document {
     Key => (upperBettiMVT,MonomialIdeal),
     Headline=>"Outputs upper bounds for the Betti numbers of a monomial ideal, based on a Mayer-Vietoris tree of it."
     Usage => "lowerBettiMVT(I)",
     Inputs => {
          MonomialIdeal
          -- each input is a hypertext list
          },
     Outputs => {
          "A Betti diagram"
          -- each output is a hypertext list
          },
     EXAMPLE {
          "R=QQ[x,y,z]",
          "I = monomialIdeal(x^2,y^2,x*y)",
          "upperBettiMVT(I)"
          },
     }

document {
     Key => [upperBettiMVT, PivotStrategy]
     Headline=>"The Pivot Strategy is the one that will be used for the computation of the Mayer-Vietoris tree."
}

document {
     Key => pseudoBettiMVT,
     Headline=>"Outputs lower and upper bounds for the Betti numbers of a monomial ideal, based on a Mayer-Vietoris tree of it."
}


document {
     Key => (pseudoBettiMVT,MonomialIdeal),
     Headline=>"Outputs lower and upper bounds for the Betti numbers of a monomial ideal, based on a Mayer-Vietoris tree of it."
     Usage => "pseudoBettiMVT(I)",
     Inputs => {
          MonomialIdeal
          -- each input is a hypertext list
          },
     Outputs => {
          "A Betti diagram in which each entry is either an integer, which in that case is the corresponding Betti number of the ideal, or a pair of integers, which in that case are a lower and an upper bound for that particular Betti number of the ideal."
          -- each output is a hypertext list
          },
     EXAMPLE {
          "R=QQ[x_1..x_6]",
          "I = monomialIdeal(x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_1)",
          "lowerBettiMVT(I)"
          "upperBettiMVT(I)"
          "pseudoBettiMVT(I)"
          },
     }

document {
     Key => [upperBettiMVT, PivotStrategy]
     Headline=>"The Pivot Strategy is the one that will be used for the computation of the Mayer-Vietoris tree."
}



TEST ///
    R = QQ[x,y,z]
    I = monomialIdeal "x2,x3y,xyz,z2"
    idealLeft(gens I, PivotStrategy => 2)
    idealLeft(gens I, PivotStrategy => 2)
    
    myMVT(1,0,gens I, PivotStrategy => 2)
         
    L = relevantNodes(fullMVT(I,PivotStrategy => 2))
    listOfPositions L
    
    pivot(gens I) 
    oo == x^2
    pivot(gens I,PivotStrategy => 2) 
    oo == z^2
    
    R = QQ[s_1..s_10]
    J = monomialIdeal (s_1..s_10)
    time relMVT(J);
    
    R = QQ[t_1..t_15]    
    J = monomialIdeal (t_1..t_15)
    time relMVT(J);
    
restart
load "MayerVietorisTrees.m2"
installPackage "MayerVietorisTrees"
load "MayerVietorisTrees.m2"
R = QQ[x,y,z]
I = monomialIdeal "x2,x3y,xyz,z2"
J = monomialIdeal "x2,y2,xy,xz,yz"
upperBettiMVT(I)
lowerBettiMVT(I)
upperBettiMVT(J)
lowerBettiMVT(J)

pseudoBettiMVT(I)
pseudoBettiMVT(J)

fullMVT(I)
M = relMVT(I)
--splitNodes M
lowerBetti
fullMVT(J)
N = relMVT(J)
relNodesGens(N)
T = splitNodes relNodesGens(N)
#(T#0)+#(T#1)
#relNodesGens(N)
projDim(J)
    
    
    
    
///

end

restart
load "MayerVietorisTrees.m2"
installPackage "MayerVietorisTrees"

-- At this point, need to compile some of the functions

projDim(J)
reg(J)

S = QQ[x,y,z]
I = monomialIdeal "x2,y2,xy"
relMVT(I,PivotStrategy => 2)
relNodesGens(relMVT(I,PivotStrategy => 2))
L = (splitNodes(oo))#0
projDimMVT(I)
regMVT I
upperBettiMVT(I)
lowerBettiMVT(I)
pseudoBettiMVT(I)

restart
collectGarbage;
load "MayerVietorisTrees.m2"
installPackage "MayerVietorisTrees"

R = QQ[x,y,z]
I = monomialIdeal "x2,y2,xy,xz,yz"
relMVT(I)
(splitNodes(relNodesGens(relMVT(I))))#1
--relNodesGens(relMVT(I))
upperBettiMVT(I)
betti res I
lowerBettiMVT(I) --Notice compatibility (repeated nodes don't matter here)

---pseudoBettiMVT:
R = QQ[x,y,z]
I = monomialIdeal "x2,y2,xy,xz,yz"
P = pseudoBettiMVT(I)

help MayerVietorisTrees
