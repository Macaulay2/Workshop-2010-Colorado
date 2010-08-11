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

RpistarLinPres M

d = -1
M = truncate(2, S^{d})
RpistarLinPres M

d = -2
M = truncate(2, S^{d})
RpistarLinPres M

M = truncate(4, S^{d})
RpistarLinPres M

d = -3
M = truncate(2, S^{d})
RpistarLinPres M

M = truncate(4, S^{d})
RpistarLinPres M

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
Rpistar M)

for i from -2 to 3 do print test1 (-i)

---------------
restart
path = append(path, "/Users/david/src/Colorado-2010/PushForward")
load "computingRpi_star.m2"
--The Boij-Soederberg examples:
kk=ZZ/101
--base space of the deformations of $O(-d)++O(d)$ on P1
--Ext^1 (O(d), O(-d)) = H^1 O(-2d) = K^(2d-1)
--We see the deformation from the presentation

--                O(-d)^{2d-1}
--          |       |               
--O(-d) -->   --> O(-d+1)^{2d}
--          |       |
--O(-d) --> E --> O(d)


defoMatrix = d->(
     A = kk[x_0..x_(2*d-2)];
     S = A[y_0,y_1];
     map(S^{{-d,1},2*d:{-d+1,0}}, S^{(2*d-1):{-d,0}}, (i,j)->(
	       if i == 0 then sub(A_j, S) else
	       if i == j+1 then S_0 else
	       if i == j+2 then S_1 else
	       0_S)
     )
)
m=defoMatrix 2
betti m
isHomogeneous m
Rpistar coker m
