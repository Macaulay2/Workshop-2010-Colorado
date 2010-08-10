-- -*- coding: utf-8 -*-
newPackage(
        "MayerVietorisTrees",
        Version => "0.1", 
        Date => "August 8, 2010",
        Authors => {{Name => "Eduardo"},
	     	    {Name => "Courtney"}},
	--CurrentDevelopers => {{Name => "Eduardo"},
	--    	                {Name => "Courtney"} };
	--PastDevelopers => { };
	--Contributors => { };
	--Acknowledgments => { };
        Headline => "A package for computing Mayer-Vietoris Trees for monomial ideals",
        DebuggingMode => true
        )

export {fullMVT,relMVT,relevantNodes}

--TO DO:
-- v0: document methods
-- v0: create relMVT
-- v0: change output for all things to (monomial, dimension, position)
-- v1: make things fast!


 ----------------------------
-- Internal Support Methods --
 ----------------------------

pivot = method(Options => {Strat => 1});  --Chooses the pivot generator for creating a MVT from a monomial ideal
pivot(Matrix) := o -> (I) -> {
     if o.Strat == 1 then {
     return first first entries I;}
     else return last first entries I;
     }

idealRight = method(Options => {Strat => 1});  --Creates the right child of node in an MVT
idealRight(Matrix) := o -> (I) -> {
     return gens (monomialIdeal I - monomialIdeal pivot(I,Strat => o.Strat));
     }

idealLeft = method(Options => {Strat => 1});   --Creates the left child of a node in an MVT
idealLeft(Matrix) := o -> (I) -> {
     return gens intersect(monomialIdeal idealRight(I,Strat => o.Strat), monomialIdeal pivot(I,Strat => o.Strat));
      -- this can be optimized (we're computing pivot 2x)
     }

myFullMVT = method(Options => {Strat => 1});   --Creates a full MVT (all nodes, not just relevant ones)
myFullMVT(Matrix,ZZ,ZZ) := o -> (M,myDim,myPos) -> {
     undone := {};
     undone = undone | {(M,0,1)};
     L := {(M,0,1)};
     while undone != {} do { A := undone#0;
	  undone = remove(undone,0);
	  J := A#0;
	  if numcols J > 1 then {
	       L1 := idealLeft(J,Strat => o.Strat);
	       L2 := idealRight(J,Strat => o.Strat);
	       L = L | {(L1,1+A#1,2*A#2)}; --relevant nodes
	       L = L | {(L2,A#1,1+2*A#2)}; --irrelevant nodes
	       if numcols L1 != 1 then {	       
		    if numcols L1 == 2 then { 
			 L11 := idealLeft(L1,Strat => o.Strat);
			 L12 := idealRight(L1,Strat => o.Strat);
			 L = L | {(L11,2+A#1,4*A#2)} | {(L12,1+A#1,1+4*A#2)};
			 }
	       	    else  {undone = undone | {(L1,1+A#1,2*A#2)}};
		    };
	       if numcols L2 != 1 then {
	       	    if numcols L2 == 2 then { 
			 L21 := idealLeft(L2,Strat => o.Strat);
			 L22 := idealRight(L2,Strat => o.Strat);
			 L = L | {(L21,1+A#1,2+4*A#2)} | {(L22,A#1,3+4*A#2)};
		    	 }
		    else {undone = undone | {(L2,A#1,1+2*A#2)}};
		    }
	  }
     }; -- \ends the "do"
     return L;
     }

myRelMVT = method(Options => {Strat => 1});    --Creates a list of only the relevant nodes in an MVT
myRelMVT(Matrix,ZZ,ZZ) := o -> (M,myDim,myPos) -> {
     undone := {};
     undone = undone | {(M,0,1)};
     L := {(M,0,1)};
     while undone != {} do { A := undone#0;
	  undone = remove(undone,0);
	  J := A#0;
	  if numcols J > 1 then {
	       L1 := idealLeft(J,Strat => o.Strat);
	       L2 := idealRight(J,Strat => o.Strat);
	       L = L | {(L1,1+A#1,2*A#2)}; --relevant nodes
	       --L = L | {(L2,A#1,1+2*A#2)}; --irrelevant nodes; not output
	       if numcols L1 != 1 then {	       
		    if numcols L1 == 2 then { 
			 L11 := idealLeft(L1,Strat => o.Strat);
			 L12 := idealRight(L1,Strat => o.Strat);
			 L = L | {(L11,2+A#1,4*A#2)};
			 }
	       	    else  {undone = undone | {(L1,1+A#1,2*A#2)}};
		    };
	       if numcols L2 != 1 then {
	       	    if numcols L2 == 2 then { 
			 L21 := idealLeft(L2,Strat => o.Strat);
			 L22 := idealRight(L2,Strat => o.Strat);
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

--splitNodes = method();     	  
--splitNodes(List) := L -> {
--     l = length L - 1;
--     L0 := (for i from 0 to l list L#i#0);
--     T := tally apply(L, i -> i#0);
--     uniqueList := apply(select(pairs T,p -> p#1 == 1), first);
--     NonRep := select(L, p -> member(p#0,uniqueList));
--     Rep := select(L, p -> not member(p#0,uniqueList));
--     (NonRep, Rep)
--     }

splitNodes = method();
splitNodes(List) := (myList) -> {
   myTally := tally apply(myList, i -> i#0);
   uniqueList := apply(select(pairs myTally, p -> p#1 == 1), first);
   nonUniqueList  := apply(select(pairs myTally, p -> p#1 > 1), first);
   repList := select(myList, p -> member(p#0,uniqueList));
   nonRepList := select(myList, p -> member(p#0,nonUniqueList));
   return (repList,nonRepList)
 }

--myMVT(ZZ,ZZ,Matrix) := o -> (pos,dimn,I) -> {  --ORIGINAL ALGORITHM
--     undone := {};
--     undone = undone | {(1,0,I)};
--     L := {(1,0,I)};
--     while undone != {} do { A := undone#0;
	--  undone = remove(undone,0);
	--  J := A#2;
	--  if numcols J > 1 then {
	--       L1 := idealLeft(J,Strat => o.Strat);
	--       L2 := idealRight(J,Strat => o.Strat);
	--       if numcols L1 > 1 then {undone = undone | {(2*A#0,1+A#1,L1)}};
	--       if numcols L2 > 1 then {undone = undone | {(1+2*A#0,A#1,L2)}};
	--       L = L | {(2*A#0,1+A#1,L1)}; --relevant nodes
	--       L = L | {(1+2*A#0,A#1,L2)}; --irrelevant nodes
	--  }
--     }; -- \ends the "do"
--     return L;
--     }

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



 ----------------------
-- Methods for Export --
 ----------------------

fullMVT = method(Options => {Strat => 1} );
fullMVT(MonomialIdeal) := o -> (I) -> {
     J := gens I;
     T := myFullMVT(J,1,0, Strat => o.Strat);
     return T;
     }
  
relMVT = method(Options => {Strat => 1} );
relMVT(MonomialIdeal) := o -> (I) -> {
     J := gens I;
     T := myRelMVT(J,1,0, Strat => o.Strat);
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

projDim = method(Options => {Strat => 1});
projDim(MonomialIdeal) := o -> (I) -> {
     myNodes := relNodesGens(relMVT(I,Strat => o.Strat));
     nonRep := first splitNodes(myNodes);
     rep := last splitNodes(myNodes);
     if maxDim(nonRep) >= maxDim(rep) then return maxDim(nonRep)
     else return (maxDim(nonRep),maxDim(rep));
     }

reg = method(Options => {Strat => 1});
reg(MonomialIdeal) := o -> (I) -> {
     myNodes := relNodesGens(relMVT(I,Strat => o.Strat));
     nonRep := first splitNodes(myNodes);
     rep := last splitNodes(myNodes);
     if maxReg(nonRep) >= maxReg(rep) then return maxReg(nonRep)
     else return (maxReg(nonRep),maxReg(rep));
     }

--totalBetti = method(); -- outputs a BettiTally

--gradedBetti = method(); -- outputs a BettiTally





beginDocumentation()
document { 
        Key => MayerVietorisTrees,
        Headline => "Headlines",
        EM "MayerVietorisTrees", " is a package that creates and manipulates Mayer-Vietoris trees for monomial ideals."
        }
--document {
  --      Key => {(MVT,MonomialIdeal),MVT},
  --      Headline => "Headline goes here...",
  --      Inputs => { {"A monomial ideal ", TT "I"} },
  --      Outputs => {{ "The relevant nodes of the Mayer-Vietoris tree of ", TT "I" }},
  --	Usage => "Usage goes here",
  --      SourceCode => {(MVT,MonomialIdeal)},
  --      EXAMPLE lines ///
  --         "Some examples of stuff"
  --      ///
  --      }

TEST ///
    R = QQ[x,y,z]
    I = monomialIdeal "x2,x3y,xyz,z2"
    idealLeft(gens I, Strat => 2)
    idealLeft(gens I, Strat => 2)
    
    myMVT(1,0,gens I, Strat => 2)
         
    L = relevantNodes(fullMVT(I,Strat => 2))
    listOfPositions L
    
    pivot(gens I) 
    oo == x^2
    pivot(gens I,Strat => 2) 
    oo == z^2
    
    R = QQ[s_1..s_10]
    J = monomialIdeal (s_1..s_10)
    time relMVT(J);
    
    R = QQ[t_1..t_15]    
    J = monomialIdeal (t_1..t_15)
    time relMVT(J);
    
restart
R = QQ[x,y,z]
I = monomialIdeal "x2,x3y,xyz,z2"
J = monomialIdeal "x2,y2,xy,xz,yz"
fullMVT(I)
M = relMVT(I)
splitNodes M

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
relMVT(I,Strat => 2)
relNodesGens(relMVT(I,Strat => 2))
splitNodes(oo)
projDim(I)
reg I
