-----------------------
----Slow Groebner bases
-----------------------
restart
time load "symm.m2"
time initSymRing(23,PreCalculateRelations => true)
time gens grbH; --Too slow..

---------------
time initSymRing(30,PreCalculateRelations => true)
time gens grbH; --Too slow..

--------------
time initSymRing(30,PreCalculateRelations => true)
time e_30%grbH; --Also slow..


-----------------------------------------------------
----Promoting from the coefficient ring to Schur ring
-----------------------------------------------------
restart
loadPackage "SchurRings"
time R = symmRing 5
S = schurRing(y,5,CoefficientRing => R)

map(S,R,apply(gens R,i-> promote(i,S))) --error "inappropriate number of degrees"
map(S,R) --error "inappropriate number of degrees"
