restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
--uninstallPackage "BGG"
--installPackage "BGG"
loadPackage "BGG"
--Elliptic singularity
kk = ZZ/101
A = kk[x_0..x_2]
S = A[y_0..y_2]
iX = minors(2, matrix{{x_0..x_2},{y_0..y_2}})
itt = iX+ideal(sum(3,i->x_i^3)) --total transform of the cone
ist = saturate(iX+ideal(sum(3,i->x_i^3)), sub(ideal(x_0..x_2),S)) --strict tr
F=directImageComplex (S^1/itt)
G=directImageComplex (S^1/ist)
F.dd
G.dd
prune(HH G)#0






restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage "BGG"

M = universalExtension({-2+d,-3+d},{2+d,3+d});
     F=directImageComplex M;
     A=ring F;
     F.dd
     
netList for d from -5 to 1 list(
M = universalExtension({-2+d,-3+d},{2+d,3+d});
F=directImageComplex M;
A=ring F;
F.dd_0)




kk=ZZ/101
A=kk[x_0..x_3]
S=A[s,t]
n=ablock({-1,-2},{1,2},S)
m=bblock({1,2},-2, S)
n||m

u
res coker transpose (n||m)
degrees source m

degrees target m

m=universalExtension({-1},{1,1})

-- Example set 1
-- 







kk = ZZ/101
d = 9
S = kk[x,y]
M = truncate(-d+2, S^{d})

M = truncate(1, S^{d})
M = truncate(2, S^{d})

directImageComplexLinPres M

d = -1
M = truncate(2, S^{d})
directImageComplexLinPres M

d = -2
M = truncate(2, S^{d})
directImageComplexLinPres M

M = truncate(4, S^{d})
directImageComplexLinPres M

d = -3
M = truncate(2, S^{d})
directImageComplexLinPres M

M = truncate(4, S^{d})
directImageComplexLinPres M

  -- answer, for d >= 0
  --  0 --> A^(d+1) --> 0
  --        0
  --
  -- d = -1:
  --  0
  -- d < -1
  --  0 --> A^(-d-1) --> 0
  --        1

restart
path = append(path, "/Users/david/src/Colorado-2010/PushForward")
load "computingRpi_star.m2"
kk = ZZ/101
A = kk[t]

d = 2
S = A[x,y]

test = d->(
M=(ideal vars S)^(d+2)*(coker map(S^{{d,-2}}, S^{{d,-5}}, matrix{{t_S^3}}));
RpistarLinPres M)

for i from -2 to 2 do print test (-i)

  -- answer, for d >= 0
  --  0 --> A^(d+1)  --> A^(d+1) --> 0 (map is mult by t^3
  --                       0
  --
  -- d = -1:
  --  0
  -- d < -1
  --  0 --> A^(-d-1) --> A^(-d-1) --> 0 (map is mult by t^3)
  --        0              -1

-----------
restart
path = append(path, "/Users/david/src/Colorado-2010/PushForward")
load "computingRpi_star.m2"

kk = ZZ/101
A = kk[t]
S = A[x,y]

test1 = d->(
M=(coker map(S^{{d,-2}}, S^{{d,-5}}, matrix{{t_S^3}}));
directImageComplex M)

for i from -2 to 3 do print test1 (-i)

---------------
--Splittings of bundles on P1

--base space of the deformations of $O(-d)++O(d)$ on P1
--Ext^1 (O(d), O(-d)) = H^1 O(-2d) = K^(2d-1)
--We see the deformation from the presentation

--                O(-d)^{2d-1}
--          |       |               
--O(-d) -->   --> O(-d+1)^{2d}
--          |       |
--O(-d) --> E --> O(d)

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
--load "computingRpi_star.m2"
loadPackage "BGG"
m=universalExtension(-2,2,-2)
S = ring m
A = coefficientRing S
M=coker m
directImageComplex  (M)
oo.dd

--make the ground field be an option! maybe also A and S.

universalExtension = method()
universalExtension(ZZ,ZZ,ZZ) := (a,b,c) -> (
     --Let Fi be the direct sum of line bundles on P1
     --F1 = O(a), F2 = O(b)
     --The script makes a module E representing the bundle that is
     --the universal extension of F2 by F1 on P^1; (so the extension is
     --  0 --> F1 --> E --> F2 --> 0.
     --The answer is defined over A[y_0,y_1] representing 
     -- P^1 x Ext(Sheaf F2,Sheaf F1).
     -- The matrix obtained has relations in total degree {c,-1}
     --assumes the existence of
--     kk := ZZ/101;
--     A := kk[x_0..x_(2*d-2)];
--     S := A[y_0,y_1];
     map(S^{{a,0},(b-c):{c+1,0}}, S^{(b-c-1):{c,-1}}, (i,j)->(
	       if i == 0 then
	            (if j<= b-a-2 then sub(A_j, S)*S_1^(c-a) else 0_S) 
		         else
	       if i == j+1 then S_0 else
	       if i == j+2 then S_1 else
	       0_S)
     )
)

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
--load "computingRpi_star.m2"
loadPackage "BGG"

a =-1
b=1
c=-2
     kk = ZZ/101
     A = kk[x_0..x_(b-a-2)]
     S = A[y_0,y_1]
m=universalExtension( a, b, c)

----------
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage "BGG"

-- on Spec A x P^1: 
--make the universal extension of O(-3) by O, and a generic
--extension of O(-2) by O, with the generic map from one to the other.
--make the map of pushforwards.

kk = ZZ/101
A=kk[a..i]
S = A[x,y]
--universal extension
mat4 = matrix"x,0,0;
     	       y,x,0;
	       0,y,x;
	       0,0,y;
	       a,b,c"
pres4 = map(S^{4:{-3,0},{-4,1}}, S^{3:{-4,0}}, mat4)
degrees pres4
isHomogeneous pres4
--the following gives an error -- why??
prune dual dual(cokernel pres4)
--viewHelp dual

mat22 = matrix"x,0,0;
     	       y,x,0;
	       0,y,x;
	       0,0,y;
	       a,b,c;
	       d,e,f;
	       g,h,i"
mat211 = map(S^{4:{-3,1}}, S^{2:{-5,0}},0)
mat212 = matrix"x,0;
     	        y,x;
		0,y"
mat211||mat212
mat22
pres2 = map(S^{4:{-3,0},3:{-4,1}}, S^{3:{-4,0},2:{-5,1}}, 
	  mat22|(mat211||mat212))

isHomogeneous pres2		
degrees pres2

H=Hom(coker pres2, coker pres4)
netList degrees H
phi = homomorphism H_{1}
phi = homomorphism H_{7}
for i from 0 to numColumns gens H -1 do (
     phi = homomorphism H_{i};
     << "-----------------------" << i << endl;
     print directImageComplex phi;
     )
directImageComplex coker pres4
directImageComplex coker pres2
directImageComplex phi

-------------------------
-- 
kk = ZZ/101
S = kk[x,y]
M = S^1
N = S^{1}
phi = map(N,M,{{x}})
directImageComplex phi
-------------------------
kk = ZZ/101
S = kk[x,y,z]
M = S^1/ideal z
N = S^{1}/ideal z
phi = map(N,M,{{x}})
directImageComplex phi



---------------------

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage "BGG"

-- on Spec A x P^1: 
--make the universal extension of O(-3) by O, and a generic
--extension of O(-2) by O, with the generic map from one to the other.
--make the map of pushforwards.

kk = ZZ/101
M = universalExtension({-4},{0})
S = ring M     
NT = universalExtension({-2},{0})
T = ring NT
inc = map(S,T, {S_0, S_1, S_2})
N = coker inc presentation NT
H = Hom(M,N)
netList degrees source presentation prune Hom(M,N)
tally degrees source presentation prune Hom(M,N)
--select (degrees source presentation prune Hom(M,N), j -> j==={2.0})
--universal extension

phi = homomorphism H_{8}

directImageComplex M
oo.dd
directImageComplex N
directImageComplex phi


---------
--phi: M\to N is the identity map,
--the map "directImageComplex psi (or phi) is NOT even a map between
--the right complexes.

tw = -3
M = universalExtension({tw},{0})
S = ring M     
NT = universalExtension({-2},{0})
T = ring NT
inc = map(S,T, {S_0, S_1, S_2})
N = coker inc presentation NT
H = Hom(M,N)

phi = homomorphism H_{0}
degrees phi
directImageComplex M
oo.dd
directImageComplex N
directImageComplex phi


------------
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage "BGG"

--M = universalExtension({-1},{0})

------simplest problem

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage "BGG"

basis(List,List,Matrix) := opts -> (lo,hi,M) -> (
     F := target M;
     G := source M;
     monsF := basis(lo,hi,F,opts);
     monsG := basis(lo,hi,G,opts);
     basM := last coefficients(matrix (M * monsG), Monomials => monsF);
     map(image monsF, image monsG, basM))


------------------
--directImageComplex(Complex)

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage("BGG", Reload =>true)
debug BGG
--complex with just one term:
A =kk[a]--a dummy var
S = A[x,y]
n=2
F = chainComplex(map(S^{{0,0}}, S^{{-n,0}}, matrix{{x^(n-1)*y}}))
F.dd_1
piF =directImageComplex F
netList apply(toList(min Eres..max Eres), i->degrees Eres_i)
--
n = -2
F1 = chainComplex(map(S^{{n+1,0}}, S^{2:{n,0}}, matrix{{x,y}}))
isHomogeneous (F1.dd_1)
F0 = F1[1]

piF0 = directImageComplex (F0)
piF0.dd_(0)
piF1 = directImageComplex (F1)
piF1.dd_1


--
F1 = chainComplex(map(S^0, S^{{n,0}}, 0), 
                 map(S^{{n,0}}, S^0, 0),
		 map(S^0,S^0,0))
F0 = F1[1]

piF0 = directImageComplex (F0)
piF1 = directImageComplex (F1)


----Koszul complex on two vars to Eagon Northcott for a 2x2 matrix
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage("BGG", Reload =>true)
debug BGG
A =kk[a,b,c,d]--a dummy var
S = A[x,y]
F = res ideal vars S
F = res ideal"ax+by,cx+dy"
directImageComplex F 
oo.dd_1

--Eagon Northcott Complex for a 2x3 matrix
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage("BGG", Reload =>true)
debug BGG
A=kk[a_(0,0)..a_(1,2)]
S = A [x_0,x_1]
M = sub(map(A^2, A^{3:-1},transpose genericMatrix(A,a_(0,0),3,2)), S)
Y = (vars S)*M
maps = apply(3, i-> 
     map( S^{binomial(3,i):{-i,-i}}, 
	  S^{binomial(3,i+1):{-i-1,-i-1}}, 
	  koszul(i+1,Y)))
netList (maps/degrees)
F = chainComplex maps -- the Koszul complex to push forward
betti (F, Weights=>{1,0})
EN = directImageComplex F
betti EN
EN.dd
--and it's dual:
betti directImageComplex(F**S^{{1,0}})

--Eagon Northcott family of Complexex for a p x q matrix
--this code produces the list of all the "Eagon-Northcott" type
--complexes for a given matrix. Try p,q = 2,6 or 3,6.
--There's a funny error msg:
--warning: clearing value of symbol p to allow access to subscripted variables based on it
--What's that from?

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
path = prepend( "/Users/mike/colo2010/PushForward",path)
loadPackage("BGG", Reload =>true)
(p,q) = (2,5)
kk = ZZ/101
A=kk[a_(0,0)..a_(p-1,q-1)]
S = A [x_0..x_(p-1)]
M = sub(map(A^p, A^{q:-1},transpose genericMatrix(A,a_(0,0),q,p)), S)

Y = map(S^1, S^{q:{-1,-1}}, (vars S)*M)
F = koszul Y
betti (F, Weights=>{1,0})
time L= for i from -1 to q-p+1 list directImageComplex(F**S^{{i,0}});
--4.5 sec for p,q = 2,6 but 50 seconds for p,q = 3,6
L/betti


-----------
--Projection from multiple projective spaces?
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
path = prepend( "/Users/mike/colo2010/PushForward",path)
loadPackage("BGG", Reload =>true)
kk= ZZ/101

A=kk[a,b]
B = A[c,d]
C = B[e,f]

--useful snippets
coefficientRing C === B
ultimate(coefficientRing, C) === kk

C1 = kk[gens (flattenRing coefficientRing C)_0][gens C]
f1 = map(C1,C)
f2 = map (coefficientRing C, coefficientRing C1)

--can f1, f2 be applied to a ChainComplex and a ChainComplexMap??

KK = koszul vars C

f1 KK
f2 



