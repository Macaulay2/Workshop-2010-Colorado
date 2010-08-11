-- PHCpack interface for NAG4M2
-- used by ../NumericalAlgebraicGeometry.m2
needsPackage "PHCpackInterface"

solvePHCpack = method(TypicalValue => List)
solvePHCpack (List,HashTable) := List => (F,o) -> (
     -- Anton: options are not used at the moment
     solveBlackBox F
     )

trackPHCpack = method(TypicalValue => List)
trackPHCpack (List,List,List,HashTable) := List => (S,T,sols,o) -> (
     -- Anton: options are not used at the moment
     trackPaths(S,T,sols,gamma=>o.gamma,tDegree=>o.tDegree)
     )

refinePHCpack = method(TypicalValue => List)
refinePHCpack (List,List,HashTable) := List => (T,sols,o) -> (
     -- Anton: options are not used at the moment
     refineSolutions(T,sols,
	  ResidualTolerance => o.ResidualTolerance, 
	  ErrorTolerance => o.ErrorTolerance,
	  Iterations => o.Iterations,
	  Bits => o.Bits)
     )

-- service functions ------------------------------------------
-- deleted, since duplicated in PHCpackInterface

/// -- refine examples
restart
needsPackage "NumericalAlgebraicGeometry"
debug PHCpackInterface
debug NumericalAlgebraicGeometry
peek loadedFiles
PHCpackInterface#"exported symbols"
NumericalAlgebraicGeometry#"exported symbols"

R = CC[x]
L = {x^2-2}
solveSystem(L, Software=>PHCpack)
refine(L, {{1.7}}, Iterations => 10, Bits => 400, ErrorTolerance => 1p400e-130, Software=>PHCpack)

R = CC_200[x,y,z]
L = {y-x^2,z-x^3,x+y+z-1}
B = solveSystem(L,Software=>PHCpack)
B = B/first
C = apply(B, b -> refinePHCpack(L, {b}, Iterations => 10, Bits => 400, ErrorTolerance => 1p400e-130))
C/first/first

-- Using higher precision
R = CC_53[x,y,z]
R200 = CC_200[x,y,z]
L = {y-x^2,z-x^3,x+y+z-.5p200}
B = solveSystem(L,Software=>PHCpack)
B = solveSystem(L)
pt = B_0_0

C = refinePHCpack(L, {pt}, Iterations => 10, Bits => 400, ErrorTolerance => 1p400e-130)
pt1 = C_0_0
pt_0
pt1_0
///

///
-- WitnessSet and monodromyBreakupPHC
restart
debug loadPackage "NumericalAlgebraicGeometry"

R = QQ[x,y,z]
I = ideal"x+y-2,y-z+3"
J = ideal"x2+y2+z2-1,xy-z2"
L = trim intersect(I,J)
RC = CC[gens R]
L = sub(L,RC)
W = witnessSet L
--W1 = generalEquations W
--W2 = addSlackVariables W1
W3s = monodromyBreakupPHC W
apply(W3s, points)
W3s/degree
peek W2
netList (ideal W2)_*
peek oo
///

///
-- cascade interface
restart
debug loadPackage "NumericalAlgebraicGeometry"

R = QQ[x,y,z,w]
I = ideal"x+y-2,y2-z+3"
J = ideal"x2+y2+z2-1,xy-z2,x2+w2"
L = trim intersect(I,J)
RC = CC[gens R]
L = sub(L,RC)
cascadePHC L

W = witnessSet L
--W1 = generalEquations W
--W2 = addSlackVariables W1
W3s = monodromyBreakupPHC W
apply(W3s, points)
W3s/degree
peek W2
see ideal W2
peek oo
///
