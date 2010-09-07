-- This is a file of examples to test the code in the
-- QuillenSuslin package.

--Ex. No Heuristic (Step by step.)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x,y]
f = matrix{{x^2,3*y+1,x+x^2*y+y^2}}
varList = {x}
currVar = y
M1 = matrix{{0,0,1},{0,1,0},{1,0,0}}
f = f*M1 -- Put monic component first.
isUnimodular(f)
I1 = ideal(2,x)
U1 = horrocks(f,y,I1)
det(U1)
f*U1
denom1 = commonDenom(U1)
ideal(denom1) == R  -- Need to compute another local solution.
I2 = ideal(2,x^2+x+1) -- Maximal ideal containing ideal(denom1).
U2 = horrocks(f,y,I2)
det(U2)
f*U2
denom2 = commonDenom(U2)
ideal(denom1,denom2) == R -- Can proceed to the patching step.
matrixList = {U1,U2}
M2 = patch(matrixList,y)
det(M2)
f = f*M2
M3 = applyRowShortcut(f)
det(M3)
f*M3
U = M1*M2*M3
det(U)


--Ex. GagoVargas (Works fine, uses shortcut 2.2.2(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{13,x^2-1,2*x-5}}
isUnimodular(f)
U = applyRowShortcut(f) -- Uses shortcut 2.2.2(2).
time applyRowShortcut(f) -- ~.016 seconds
det(U)
f*U


--Ex. LaubenbacherWoodburn (Works fine.)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x^2*y+1,x+y-2,2*x*y}}
isUnimodular(f)
U = applyRowShortcut(f)
det(U)
f*U


--Ex1. Yengui (Works fine, uses shortcut 2.2.2(1).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x-4*y+2,x*y+x,x+4*y^2-2*y+1}}
isUnimodular(f)
U = applyRowShortcut(f)
det(U)
f*U


--Ex.2 Yengui (Works fine, uses shortcut 2.2.2(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{x^2+2*x+2,3,2*x^2+2*x}}
U = applyRowShortcut(f) -- Uses shortcut 2.2.2(2).
det(U)
f*U


--Ex.3 Yengui (Works fine, uses shortcut 2.2.2(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x+y^2-1,-x+y^2-2*x*y,x-y^3+2}}
isUnimodular(f)
U = applyRowShortcut(f)
time applyRowShortcut(f) -- ~.016 seconds
det(U)
f*U


--Ex. Park (Doesn't work, uses shortcut 2.2.1(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x,y,z]
f = matrix{{1-x*y-2*z-4*x*z-x^2*z-2*x*y*z+2*x^2*y^2*z-2*x*z^2-2*x*z^2-2*x^2*z^2+2*x*z^2+2*x^2*y*z^2,2+4*x+x^2+2*x*y-2*x^2*y^2+2*x*z+2*x^2*z-2*x^2*y*z,1+2*x+x*y-x^2*y^2+x*z+x^2*z-x^2*y*z,2+x+y-x*y^2+z-x*y*z}}
U = applyRowShortcut(f) -- Uses shortcut 2.2.1(2).
det(U)
f*U


--Ex. Van den Essen (No shortcut method works.)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[t,x,y,z]
f = matrix{{2*t*x*z+t*y^2+1,2*t*x*y+t^2,t*x^2}}


--Ex. CoxLittleOShea10 (Works fine, uses shortcut 2.2.2(1).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{1+x,1-y,x*(1+y)}}
isUnimodular(f)
U = applyRowShortcut(f)
det(U)
f*U


--Ex. CoxLittleOShea27 (Works fine, uses shortcut 2.2.2(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{1+x*y+x^4,y^2+x-1,x*y-1}}
g = map(R^1) // f
isUnimodular(f)
U = applyRowShortcut(f)
time applyRowShortcut(f) -- ~.012 seconds
det(U)
f*U


--Ex1. Brett (Slightly bigger example, works fine, uses (p-1) x p shortcut.)
restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{1,-2*x*y,-x-y+2},{-1/2*x,x^2*y+1,1/2*x^2+1/2*x*y-x}}
isUnimodular(f)
U = qsAlgorithm(f)
time qsAlgorithm(f) --.004 seconds both ways.
det U
f*U


--Ex2. Brett (Testing Fabianska shortcut 2.2.1(3).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x]
f = matrix{{x^2+1,x-2,0}} -- Row contains a zero.
U = applyRowShortcut(f)
det(U)
f*U
f = matrix{{x^2+1,x-2,x^2+3,x-3}} -- Row contains a redundant entry.
U = applyRowShortcut(f)
det(U)
f*U


-- Testing 'horrocks':

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x,y]
f = matrix{{y^2+x^2*y+x,3*y+1,x^2}}
I = ideal(2,x)
(U,denom) = horrocks(f,y,I)
time horrocks(f,y,I) -- ~.05 seconds
det(U)
f*U

f = matrix{{1,x^2+1,x-2}} -- Test for deg(f1) = 0.
(U,denom) = horrocks(f,y,I)
det(U)
f*U

f = matrix{{y+6,y+5}} -- Test for nCol = 2.
(U,denom) = horrocks(f,y,I)
det(U)
f*U

f = matrix{{2,x^2+1,x-2}} -- Test for error: not monic.
(U,denom) = horrocks(f,y,I)

f = matrix{{y+6,y+4}} -- Test for error: not unimodular.
isUnimodular(f)
(U,denom) = horrocks(f,y,I)
