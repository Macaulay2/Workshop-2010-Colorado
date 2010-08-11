-- Example set 1
-- 
restart
path = append(path, "/Users/david/src/Colorado-2010/PushForward")
load "computingRpi_star.m2"


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
m=universalExtension 2
S = ring m
A = coefficientRing S
coker m
directImageComplex  (S^{{-1,0}}**coker m)
oo.dd

--make the ground field be an option! maybe also A and S.


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
     kk := ZZ/101;
     A := kk[x_0..x_b-a-2];
     S := A[y_0,y_1];
numgens A
m=universalExtension( a, b, c)
