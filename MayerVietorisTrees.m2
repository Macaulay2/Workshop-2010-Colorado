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

export {MVT}

 ----------------------------
-- Internal Support Methods --
 ----------------------------

pivot = method(Options => {Strat => 1});
pivot(Matrix) := o -> (I) -> {
     if o.Strat == 1 then {
     return first first entries I;}
     else return last first entries I;
     }

idealRight = method(Options => {Strat => 1}); 
idealRight(Matrix) := o -> (I) -> {
     return gens (monomialIdeal I - monomialIdeal pivot(I,Strat => o.Strat));
     }

idealLeft = method(Options => {Strat => 1});
idealLeft(Matrix) := o -> (I) -> {
     return gens intersect(monomialIdeal idealRight(I,Strat => o.Strat), monomialIdeal pivot(I,Strat => o.Strat));
      -- this can be optimized (we're computing pivot 2x)
     }

myMVT = method(Options => {Strat => 1});
myMVT(ZZ,ZZ,Matrix) := o -> (pos,dimn,I) -> {
     undone := {};
     undone = undone | {(1,0,I)};
     L := {(1,0,I)};
     while undone != {} do { A := undone#0;
	  undone = remove(undone,0);
	  J := A#2;
	  if numcols J > 1 then {
	       L1 := idealLeft(J,Strat => o.Strat);
	       L2 := idealRight(J,Strat => o.Strat);
	       if numcols L1 >1 then {undone = undone | {(2*A#0,1+A#1,L1)}};
	       if numcols L2 >1 then {undone = undone | {(1+2*A#0,A#1,L2)}};
	       L = L | {(2*A#0,1+A#1,L1)}; --relevant nodes
	       L = L | {(1+2*A#0,A#1,L2)}; --irrelevant nodes
	  }
     }; -- \ends the "do"
     return L;
     }

 ----------------------
-- Methods for Export --
 ----------------------
 
MVT = method(Options => {Strat => 1} );
MVT(MonomialIdeal) := o -> (I) -> {
     J := gens I;
     T := myMVT(1,0,J,Strat=>o.Strat);
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



beginDocumentation()
document { 
        Key => MayerVietorisTrees,
        Headline => "Headlines",
        EM "MayerVietorisTrees", " is a package that does something."
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
    idealLeft(gens I,Strat => 2)
    idealLeft(gens I,Strat => 2)
    
    pivot(gens I) 
    oo == x^2
    pivot(gens I,Strat => 2) 
    oo == z^2
    
///

end

restart
installPackage "MayerVietorisTrees"
R = QQ[x,y,z]
I = monomialIdeal "x2,x3y,xyz,z2"
    
MVT(I)
relevantNodes(MVT(I))

L = {(1,2,3),(4,2,1),(3,3,3),(2,3,4)}
print L#2#0
length L
