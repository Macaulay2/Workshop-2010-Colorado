--In this example we study the direct of two sheaves on 
--the resolution of singularities of an elliptic surface
--singularity: the structure sheaf of the strict transform
--and the structure sheaf of the total transform of the singular
--point. We push these forward to the local ring of the singularity
--itself. Therefore we use the package local.m2 in Macaulay2, which
--makes use of a ring and a maximal ideal which is declared by
--the command "setMaximalIdeal". This script corresponds to the
--examples in section 5.7 of "Beilinson Monad and Direct Image
--for Families of Coherent Sheaves" by David Eisenbud and Frank-Olaf
--Schreyer (posted on arXiv.org).


restart
load "local.m2"
load "computingRpi_star.m2"

kk=ZZ/101 -- the ground field
A1=kk[a,b,c,Degrees=>{3:{2,0}}]
--I=ideal{a*b*c+a^4+b^4+c^4} -- could serve as another example, but 
--takes much longer
I=ideal{a^3+b^3+c^3} 
A=A1/I -- coordinate of an elliptic singularity
setMaxIdeal(ideal(a,b,c))

-- preparations for the blow-up
S1=kk[a,b,c,x_0,x_1,x_2,Degrees=>{3:{2,0},3:{1,1}}]
xx1=matrix{{x_0,x_1,x_2}}
S=S1/substitute(I,S1)
setMaxIdeal(ideal(a,b,c,x_0,x_1,x_2))
xx=substitute(xx1,S)

Itotal=minors(2,matrix{{a,x_0},{b,x_1},{c,x_2}})
Istrict= saturate(Itotal,ideal(a,b,c))
transpose gens Istrict

--preparation for the push-down
E1=kk[a,b,c,e_0,e_1,e_2,Degrees=>{3:{2,0},3:{1,1}},SkewCommutative=>toList(3..5)]
E=E1/substitute(I,E1)
setMaxIdeal(ideal(a,b,c,e_0,e_1,e_2))
ee=matrix{{e_0,e_1,e_2}}

--push-down of the strict transform
M1=coker substitute(gens Istrict,S)
d=4
M= presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}}
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx);
P=coker N
time fPstrict=(localResolution(P,LengthLimit=>2*d))[d-1]**E^{{d-1,d}}
bettiT dual fPstrict
--  index: -5 -4 -3 -2 -1  0  1  2 3
--     -1: 18 15 12  9  6  3  1  . .
--      0: 33 27 21 15  9  4  3  6 9
--      1: 27 21 15  9  4  4  9 15 .
--      2: 21 15  9  4  4  9 15  . .
--      3: 15  9  4  4  9 15  .  . .
--      4:  9  4  4  9 15  .  .  . .
--      5:  4  4  9 15  .  .  .  . .
--      6:  4  9 15  .  .  .  .  . .
--      7:  9 15  .  .  .  .  .  . .
--      8: 15  .  .  .  .  .  .  . 
 
--push-down of the total transform
M1=coker substitute(gens Itotal,S)
d=4
M=presentation localPrune (((ideal xx)^d)*M1)**S^{{0,d}};
N=presentation localPrune coker symmetricToExteriorOverA(M,ee,xx);
P=coker N
fPtotal=(localResolution(P,LengthLimit=>2*d))[d-1]**E^{{d-1,d}}
bettiT dual fPtotal
--    index: -5 -4 -3 -2 -1 0 1  2  3
--       -2: 15 10  6  3  1 . .  .  .
--       -1: 24 15  8  3  . . .  .  .
--        0: 10  6  3  1  1 1 3  6 10
--        1:  .  .  .  .  . 3 8 15  .
--        2:  .  .  .  .  1 3 6  .  .

-- comparing R^0pi_* O_total(3) and R^0pi_* O_strict(3)
Rtotal=degreeZeroPart(fPtotal**E^{{0,-3}},A)
Rstrict=degreeZeroPart(fPstrict**E^{{0,-3}},A)
-- 















