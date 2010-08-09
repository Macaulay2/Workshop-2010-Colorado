-- Example set 1
-- 
restart
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
