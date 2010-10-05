--Pure resolutions.
{*basis(List,List,Matrix) := opts -> (lo,hi,M) -> (
     F := target M;
     G := source M;
     monsF := basis(lo,hi,F,opts);
     monsG := basis(lo,hi,G,opts);
     basM := last coefficients(matrix (M * monsG), Monomials => monsF);
     basM)
*}
needsPackage "BGG"

--first, the multilinear regular sequence
pars = (k, mm) -> (
     --list of ways of writing k as a sum of #mm
     --non-negative numbers of which the i-th is <=mm_i
     ell := #mm;
     if k<0 or ell <1 then error("needs arguments k,ell with k>=0, ell >0");
     if k == 0 then return {toList(ell:0)};
     if ell == 1 and  k<= mm_(ell-1) then return {{k}};
     if ell == 1 and k>mm_(ell-1) then return{{}}; 
     P := {};
     for i from 0 to min(k,mm_0) do
         P = P | apply(
	      pars(k-i,drop(mm,1)), 
	               s->prepend(i,s)
		       );
    select(P,p->#p == #mm))

multilinearSymmetricSequence = method()
multilinearSymmetricSequence List := mm ->(
     M := sum mm; -- total dimension
     ell := #mm;  -- number of sets of vars
     for k from 0 to M list(
	  P := pars(k,mm);
	  sum(P, p -> product(ell, i->x_(i, p_i))
	  ))
)

multilinearSymmetricSequence (Ring,List) := (T,mm) ->(
     M := sum mm; -- total dimension
     ell := #mm;  -- number of sets of vars
     for k from 0 to M list(
	  P := pars(k,mm);
	  sum(P, p -> product(ell,i-> sub(x_(i, p_i), T))
	  ))
)


-- Some pure resolutions with degree 2 maps in 2 places
-- The module resolved is of finite length, over a ring with n vars.
-- The degree 2 maps will be maps indexed 0< p_0 < p_1 < n, and the 
-- degrees of these maps will be e_0 and e_1. 
-- The restriction p_1<n comes from the way the script is written
-- at the moment.

pureRes = method()
pureRes(Ring,List,List) := (A,p,e) -> (
     --n = number of variables = length of resolution
     --p = {p0,p1} where to make the two non linear steps
     -- with 0 < p0 < p1 < n
     --e = {e_0,e_1} jumps in the degrees at p0 and p1
     --(so F_(p_0) is gen in deg p_0+e_0, and
     --F_(p_1) is gen in deg p_0+e_0+e_1,
     --and the maps are of degrees e_0+1 and e_1+1
     n := numgens A;
     if #p!= 2 then error("second arg  must be a list of length 2");
     if #e!= 2 then error("third arg  must be a list of length 2");   
--     if p_0<0 or or p_1<0 or p_1< p_0 or p_1>= nor p_0>=n then 
--         error("need 0<p_0<=p_1<numgens A");
     if e_0<0 or e_1 < 0 then error("e_i must be positive");
     kk := coefficientRing A;
     S := A[x_(1,0)..x_(1,e_0)];
     B := kk[x_(0,0)..x_(0,n-1),x_(1,0)..x_(1,e_0)];
     use S;
     gotoS := map(S,B, sub((vars A),S)|matrix{{x_(1,0)..x_(1,e_0)}});
     T := B[x_(2,0)..x_(2,e_1)];

     params = matrix {multilinearSymmetricSequence(T, {n-1,e_0,e_1})};
     len := n+e_0+e_1;
     kn := T^{{p_1+e_0-1,0}}**koszul(len,params);

     D := directImageComplex kn;
     DS := gotoS(D_(-e_1));
     pi1kn := map(S^{(rank target DS):{-len+1, -len+1}},
	  S^{(rank source DS):{-len, -len}}, DS);
     twistedpi1kn = pi1kn**S^{{p_0-1,0}};

     D2 := directImageComplex twistedpi1kn;

     (dual res coker dual D2_(-e_0))[-n]
     )

end
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
load "pure-resolutions.m2"

A = kk[vars(0..4)]
betti (P = pureRes(A, {2,2},{3,1}))

A = kk[a,b,c,d]
betti (P=pureRes(A,{1,3},{2,1}))
betti (Q=pureRes(A,{1,1},{3,0}))
I21 = ann coker P.dd_1
I12 = ann coker Q.dd_1
I12==I21
degree coker P.dd_1
degree coker Q.dd_1
degree annihilator coker P.dd_1
degree annihilator coker Q.dd_1
apply(10, i->hilbertFunction(i,I21))

M = coker Q.dd_1
prune Hom(M,M)
degrees oo
{*
Possible conjectures:
1. the degree of the annih divides the degree of the module.
2. stronger: the generic module is defined over a domain.
3. the degree of the module and the actual annihilator are
independant of the position of the jumps.
4. the multiplier in 1 must be the multiple of the E-N that
you get by taking pureRes(A, {1,1}, e). This seems to be a direct sum.
5. the multiplier seems to be {e_1+e_2\choose e_1}
6. Maybe in general multinomial(e_1+e_2..., {e_1, e_2,...}) is the
factor.
*}


