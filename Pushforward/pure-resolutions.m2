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
     P = {};
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

end
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
load "pure-resolutions.m2"
debug BGG

mm = {2,2} -- corresponds to P^(mm_0) x P^(mm_1) x ...

kk = ZZ/101
S = kk[x_(0,0)..x_(0,mm_0)][x_(1,0)..x_(1,mm_1)]
n = matrix {multilinearSymmetricSequence mm}
kn = koszul(mm_0+mm_1+1,n);

--Eagon-Northcott complex
D=directImageComplex kn
betti dual res coker dual D_(-2)

--Buchsbaum-Rim complex
time D=directImageComplex (kn**S^{{1,0}})
betti dual res coker dual D_(-2)
