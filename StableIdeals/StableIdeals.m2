-- -*- coding: utf-8 -*-
--=========================================================================--
--=========================================================================--
--=========================================================================--

newPackage(
     "StableIdeals",
     Version => "0.1", 
     Date => "August 8, 2010",
     Authors => {
	  {Name => "Jason McCullough", Email => "jmccullo@math.ucr.edu", HomePage => "http://www.math.ucr.edu/~jmccullo"}
	  },
     Headline => "Computations for weakly stable, stable, and strongly stable ideals",
     DebuggingMode => true
     )

--=========================================================================--
     
export{maxVar,isWeaklyStable} 
        
--=========================================================================--
needsPackage "LexIdeals"

maxVar = method()
maxVar(RingElement) := (m) -> (
     -- Check that m is a monomial
     if length terms m > 1 then error "Expected a monomial";
     
     -- Check that ring is a polynomial ring?
     R := ring m;
     if not isPolynomialRing R then error "Expected element in a polynomial ring";
     
     v := flatten entries vars R;
     lastVar := 0_R;
     for x in v do(
	  if m % ideal(x) == 0 then lastVar = x;
	  );
     lastVar
     )

isWeaklyStable = method()
isWeaklyStable(MonomialIdeal) := (I) -> (
     all(ap,i->isLexIdeal(i))
     )
