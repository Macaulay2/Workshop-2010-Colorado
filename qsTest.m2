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


--Ex. LaubenbacherWoodburn (Works fine, uses shortcut 2.2.1(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{x^2*y+1,x+y-2,2*x*y}}
U = applyRowShortcut(f) -- Uses shortcut 2.2.1(2).
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


--Ex. Park (Works fine, uses shortcut 2.2.1(2).)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x,y,z]
f = matrix{{1-x*y-2*z-4*x*z-x^2*z-2*x*y*z+2*x^2*y^2*z-2*x*z^2-2*x*z^2-2*x^2*z^2+2*x*z^2+2*x^2*y*z^2,2+4*x+x^2+2*x*y-2*x^2*y^2+2*x*z+2*x^2*z-2*x^2*y*z,1+2*x+x*y-x^2*y^2+x*z+x^2*z-x^2*y*z,2+x+y-x*y^2+z-x*y*z}}
changeVar(f,{x,y},z) -- No component of the row is monic in any of the variables.
isUnimodular(f)
ideal(f_(0,1),f_(0,2)) == R
U = applyRowShortcut(f) -- Uses shortcut 2.2.1(2).
det(U)
f*U


--Ex. Van den Essen (No shortcut method works.)

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[t,x,y,z]
f = matrix{{2*t*x*z+t*y^2+1,2*t*x*y+t^2,t*x^2}}
(g,phi) = changeVar(f,z)
phi(g)
U = qsAlgorithmRow(f)
det(U)
f*U

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


-- Testing normalization process.

-- Testing the special case n = 2.
restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x]
f = matrix{{2*x,2*x-1}}
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,x)
det(M)
f*M

-- Testing case where f already has a monic component.
-- The routine moves the lowest degree monic component to
-- the front.
restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{3*x*y^2+2*x*y+3,y^3+2*x^2*y+4,y^2}} -- The last entry is monic in y of degree 2.
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,y)
det(M)
f*M
sub(f*M,subs) -- The first component is now the smallest degree component that was monic in y.

-- Testing the case where f contains a monic component
-- in a different variable.  The routine finds the smallest
-- degree where this happens and moves this to the front
-- and makes the appropriate substitution.
restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[t,x,y,z]
-- The second component is monic in t of degree 2.
f = matrix{{2*t*x*z+t*y^2+1,2*t*x*y+t^2,t*x^2}} -- Van den Essen example.
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,z)
det(M)
f*M
g = sub(f*M,subs) -- The first component of the row is now monic in z.
-- Now we could use the horrocks method on this to find a local solution.
U = horrocks(g,z,ideal(t,x,y))
commonDenom(U)
sub(det(U),R) % ideal(t,x,y)
g*U

-- Redundant row entry, so changeVar can use a shortcut method.
restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x,y,z]
f = matrix{{1-x*y-2*z-4*x*z-x^2*z-2*x*y*z+2*x^2*y^2*z-2*x*z^2-2*x*z^2-2*x^2*z^2+2*x*z^2+2*x^2*y*z^2,2+4*x+x^2+2*x*y-2*x^2*y^2+2*x*z+2*x^2*z-2*x^2*y*z,1+2*x+x*y-x^2*y^2+x*z+x^2*z-x^2*y*z,2+x+y-x*y^2+z-x*y*z}}
isUnimodular(f)
(M,subs,invSubs) = changeVar(f,z) -- One of the row entries is redundant so we can use a shortcut method.
det(M)
g = sub(f*M,subs)


-- Over QQ. No component of the row is monic in x or y or is just a constant times x or y.
-- Also all 3 components are needed to generate the entire ring.
restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = QQ[x,y]
f = matrix{{2*x^2*y+x*y+1,3*x^2*y^2+x*y,5*x^3*y^2+x*y}}
isUnimodular(f)
--changeVar(f,y)

-- This would be the result if we just used 1/2 to make
-- the highest total degree term of f1 monic, then used
-- the appropriate change of variables.
M = matrix{{1/2,0,0},{0,1,0},{0,0,1}}
subs = matrix{{x+y,y}}
invSubs = matrix{{x-y,y}}
g = f*M
g = sub(g,subs)
leadCoeffVar(g_(0,0),y)
U = horrocks(g,y,ideal(x)) -- U takes up about 150 lines of output.
commonDenom(U)
sub(det(U),R) % ideal(x)
g*U

-- This would be the result if instead we use the relation
-- in ZZ on the leading coefficients of f2 and f3 (avoiding
-- rational numbers) and then make the change of variables.
subs = matrix{{x+y,y}}
invSubs = matrix{{x-y,y}}
M = matrix{{1,0,0},{2*x,1,0},{-1,0,1}}
g = f*M
g = sub(g,subs)
leadCoeffVar(g_(0,0),y)
U = horrocks(g,y,ideal(x)) -- U takes up about 320 lines of output.
commonDenom(U)
sub(det(U)*commonDenom(matrix{{det(U)}}),R) % ideal(x)
g*U

restart;
load("Documents/M2 Files/QuillenSuslin.m2");
R = ZZ[x,y]
f = matrix{{2*x^2*y+2*x*y+1,2*x^2*y^2+2*x*y,2*x^3*y^2+x*y}}
isUnimodular(f)
M = matrix{{1,0,0},{x^2,1,0},{-x,0,1}}
g = f*M


R = ZZ[x]

f = matrix{{2*x^3+2*x^2+1,2*(x^4+x^2),2*(x^5+x^2)}}
isUnimodular(f)
map(R^1) // f
