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
