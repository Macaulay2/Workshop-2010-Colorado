-- This crashes M2, as notices by DE and MES
-- svn 11506.

restart
--path = append(path, "/Users/david/src/Colorado-2010/PushForward")
load "computingRpi_star.m2"
kk=ZZ/101
A = kk[s,t]
S = A[x_0..x_2] -- ring of P^2_A
describe S
degrees S
degree s_S
I=intersect(ideal(x_0), ideal (s*x_0-t*x_1, x_2)) -- ideal of a point moving across a line
M = S^{{2,0}}**module I
RpistarLinPres M

-- the above problem is almost certainly coming from this:
E = kk[e,f,SkewCommutative => true]
res(coker vars E, LengthLimit=>0)
res(coker vars E, LengthLimit=>-1)
