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
