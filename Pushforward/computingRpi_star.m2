-- This script serves as preliminary version of a Macaualy2 package BGG
-- for direct image complexes based on the paper 
-- "Beilinson Monad and Direct Image for Families of Coherent Sheaves" 
--by David Eisenbud and Frank-Olaf Schreyer (posted on arXiv.org). 
--The BGG package is currently under construction and will appear
--as part of a future release of Macaulay2. (Sept 26, 2006). 


selectComponent=(L,k)->(apply(L,c->c#k))

bettiT=method()
bettiT(ChainComplex):=(F)->(
--writes the betti table of a bigraded Tate resolution (with the maps 
--going from right to left, as in the usual betti command)
--using the SECOND degrees instead of the first.
     a:=min F;b:=max F;
     btt:=ZZ/3[tt];
     bT:=new ChainComplex;
     bT.ring=btt;
     apply(a..b,i->bT#i=btt^(-selectComponent(degrees (F_i),1)));
     betti bT
     )     


symmetricToExteriorOverA=method()
symmetricToExteriorOverA(Matrix,Matrix,Matrix):= (m,e,x) ->(
--this function converts between a  presentation matrix m with 
--entries m^i_j of degree deg_x m^i_j = 0 or 1 only 
--of a module over a symmetric algebra A[x] and the linear part of the
--presentation map for the module 
--    P=ker (Hom_A(E,(coker m)_0) -> Hom_A(E,(coker m)_1))
--over the  exterior algebra A<e>.
--                                 Berkeley, 19/12/2004, Frank Schreyer.
     S:= ring x; E:=ring e;
     a:=rank source m;
     La:=degrees source m;
     co:=toList select(0..a-1,i->  (La_i)_0==0);
     M0:=coker substitute(m_co,vars E);
     M:=coker m;
     m1:=presentation (ideal x * M);
-- script uses the fact that the generators of ideal x* M are ordered
---as follows
-- x_0 generators of M,x_1*generators of M, ...
     b:=rank source m1;
     Lb:=degrees source m1;     
     cob:=toList select(0..b-1,i->  (Lb_i)_0==1);
     M1:=coker substitute(m1_cob,vars E);
     F:=substitute(id_(target m),vars E);
     G:=e_{0}**F;
     n:=rank source e -1;
     apply(n,j->G=G|(e_{j+1}**F)); -- (vars E)**F
     phi:=map(M1,M0,transpose G)
     --presentation prune ker phi
     )

symmetricToExteriorOverA(Module) := M -> (
     --M is a module over S = A[x0...].  must be gen in x-degree 0,
     --related in x-degree 1
     S := ring M;
     xvars := vars S;
     A := coefficientRing S;
     if not S.?Exterior then(
	  --S.Exterior = exterior alg over A on dual vars to the vars of S (new vars have deg = {-1,0})
	  S.Exterior = A[Variables => numgens S, SkewCommutative => true, Degrees=>{numgens S:-1}]
	  );
     E := S.Exterior;
     symmetricToExteriorOverA(presentation M, vars E, vars S)
     )

degreeZeroPart=(T,A)->(
--Takes a (doubly) graded free complex over E (the exterior algebra 
--over a ring A, where the variables of E have grading {1,1} and {2*,0}) 
--and extracts the the degree {*,0} part of T \tensor_E A, 
--a complex of free A-modules.
--                  Berkeley, 18/12/2004, David Eisenbud, Frank Schreyer. 
     a:=min T;
     b:=max T;
     piT:=new ChainComplex;
     piT.ring=A;
     bj:=0;aj:=0;LLj:={};Lj:=LLj;co:={};ro:={};
     apply(a..b,j->(bj=rank T_j;
	       LLj=select(degrees T_j,d->d#1==0);
	       LLj=apply(LLj,d->-d);
	       piT#j=A^LLj));
     apply(a+1..b,j->(
	       aj=rank  T_(j-1);
	       bj=rank T_j;
	       Lj=degrees T_(j-1);
	       LLj=degrees T_(j);
	       co=toList select(0..aj-1,i->(Lj#i)#1==0);
	       ro=toList select(0..bj-1,i->(LLj#i)#1==0);
	       piT.dd#j=substitute(((T.dd_j)^co)_ro,A)));
     piT)

RpistarLinPres = method()
RpistarLinPres(Module) := (M) -> (
     -- assumption: M has x-linear resolution, with all generators
     -- in the same x-degree, in a ring A[x0,x1,...]
     regM = first degree M_0;
     S := ring M;
     xm = regM * degree(S_0);
     phi = symmetricToExteriorOverA(M ** S^{xm});
     E := ring phi;
     FF = res( image phi, LengthLimit => max(1,1+regM));
     complete FF;
     FF = E^{-xm} ** FF[regM];
     FF0 = degreeD(0, FF);
     toA := map(coefficientRing E,E,DegreeMap=> i -> drop(i,1));
     --we should truncate away the terms that are 0, and (possibly) the terms above the (n+1)-st
     toA FF0
     )


Rpistar = method()
Rpistar Module := (M) -> (
     F = RpistarLinPres truncateMultiGraded(regularityMultiGraded M, M);
     --now just show the relevant part of F
     G:=new ChainComplex;
     n := numgens ring M;
     for i from -n+1 to 1 do(
	  G.dd_i = F.dd_i);
     G
     )
     -- M is a graded A[x0,...xn] module, of x-regularity m.
     -- returns an A-complex representing R pi_* (M~), where pi
     -- is the map Spec A x P^n --> Spec A.

     --m := regularity M; -- we think this is the x-regularity.
     
     -- (1) truncate M in degrees = m in x variables
     -- (2) then apply Rpistar0regular to M(m), 
     --     obtaining a complex FF over A.
     -- (3) return FF[-m]

directImageComplex = method(Options => {Regularity=>null})
directImageComplex Module := opts -> (M) -> (
     S := ring M;
     regM := if opts.Regularity === null then regularityMultiGraded M
          else opts.Regularity;
     degsM := degrees M/first;
     if max degsM > regM then error("regularity is higher than you think!");
     N := if min degsM === regM then M else truncateMultiGraded(regM,M);

     xm = regM * degree(S_0);
     phi = symmetricToExteriorOverA(N ** S^{xm});
     E := ring phi;
     F = complete res( image phi, LengthLimit => max(1,1+regM));
     F = E^{-xm} ** F[regM];
     F0 = degreeD(0, F);
     toA := map(coefficientRing E,E,DegreeMap=> i -> drop(i,1));
     --we should truncate away the terms that are 0, and (possibly) the terms above the (n+1)-st
     F0A := toA F0;
     G:=new ChainComplex;
     G.ring = ring F0A;
     n := numgens ring M;
     for i from -n+1 to 1 do(
	  G.dd_i = F0A.dd_i);
     G
     )


truncateMultiGraded = method()
truncateMultiGraded (ZZ, Module) := (d,M) -> (
     --Assumes that M is a module over a polynomial ring S=A[x0..xn]
     --where the x_i have first-degree 1.
     --forms the submodule generated in x-degrees >= d.
     S := ring M;
     kk := ultimate (coefficientRing, S);
     S0 := kk[Variables => numgens S];
     f := map(S,S0, vars S);
     L := (degrees M)/first;
     Md := image M_{};
     scan(#L, i-> 
	  if L#i >= d then Md = Md + image M_{i} 
	  else Md = Md+((ideal f(basis(d-L#i, S0^1)))*(image M_{i})));
     Md
     )

regularityMultiGraded = method()
regularityMultiGraded (Module) := (M) -> (
     S := ring M;
     (R,f) := flattenRing S;
     deglen := #degree R_0;
     w := flatten {1,toList(deglen-1:0)};
     regularity (coker f presentation M, Weights=>w)
     )

defoMatrix = d->(
     --makes the presentation matrix of the universal extension of O(d) by O(-d) on P^1
     A = kk[x_0..x_(2*d-2)];
     S = A[y_0,y_1];
     map(S^{{-d,1},2*d:{-d+1,0}}, S^{(2*d-1):{-d,0}}, (i,j)->(
	       if i == 0 then sub(A_j, S) else
	       if i == j+1 then S_0 else
	       if i == j+2 then S_1 else
	       0_S)
     )
)
end	      
--------------------------------
restart
path = append(path, "/Users/david/src/Colorado-2010/PushForward")
load "computingRpi_star.m2"

kk=ZZ/101
A = kk[t]
S = A[x,y]
I = module ideal (x^2, y^4, t^2,t)

for d from -3 to 1 do print regularityMultiGraded (S^{{d,0}}**I)
for d from -3 to 1 do print Rpistar (S^{{d,0}}**I)
---------------------------------

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

M = module I
Rpistar0regular M


phi=symmetricToExteriorOverA M
E=ring phi
FF=res image phi
FF.dd
GG = (E^{{-3,0}}** FF[2])
betti GG

GG0 = degreeD(0, GG)
isHomogeneous GG0
GG0.dd

toA = map(A,E,DegreeMap=>i -> drop(i,1))
GGA = toA GG0
isHomogeneous GGA
HH GGA
toA GG.dd_1

betti GGA
isHomogeneous M
betti (F=res M)
F.dd
regularity M

-- example 5.1 

load "vectorBundlesOnPP1.m2"
L={1,3}
kk=ZZ/101
M=setupDef(L,kk)
N=symmetricToExteriorOverA(M,ee,xx)
fN=res(coker N,LengthLimit=>3)
bettiT dual fN
--  index: -3 -2 -1 0
--     -2:  4  2  1 .
--     -1:  .  1  2 4
Rpi=degreeZeroPart(fN[2]**E^{{0,2+1}},A)
Rpi.dd_0
----------------------
--general method
installPackage "BGG"
viewHelp BGG
RpiStar = method()
Rpi* (Module) := M -> (
     --If M is a graded module over a tower ring S=A[x], with the degrees of the vars x all = 1,
     --the script takes the degree zero part of the zero-th differential in the Tate resolution
     --associated to M.
     --To do this it  makes the exterior algebra E:=A[e] in exterior variables corresponding
     --to the variables of S, and the 
     --map b:=BGG(i, M, E), where i = 1 + regularity M.
     --(this should be the first linear map in the Tate resolution associated to M.)
     --the (i+1)-st differential in the resolution of coker b is the zero-th differential in the Tate 
     --resolution.
     reg = regularity M
     numvars = numgens ring M
     AA = coefficientRing ring M     
     EE = AA[e_0..e_(numvars-1), SkewCommutative => true]
     --need to make the next line work!
     bgg(reg+1, M, E)

///
A = kk[s,t]
S = A[x_0..x_2] -- ring of P^2_A
M = module intersect(ideal x_0, ideal (s*x_0-t*x_1, x_2)) -- ideal of a point moving across a line
betti res M

-------

restart
