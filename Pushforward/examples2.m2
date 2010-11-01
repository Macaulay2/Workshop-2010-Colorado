--files to produce pure resolutions as direct images of 
--twised Koszul complexes. Both the sparse sop and arbitrary
--multilinear sop's are implemented.


partitions(ZZ, List) := (k, mm) -> (
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
	      partitions(k-i,drop(mm,1)), 
	               s->prepend(i,s)
		       );
    select(P,p->#p == #mm))

projectiveProduct = method()
projectiveProduct(Ring, List) := (A,D) -> (
     --Takes a list of dimensions D = d_1..d_r
     --and makes the  product 
     --P_A^{d_1}x..xP_A^{d_r} 
     --of projective spaces over the base A, as a tower ring.
     --Returns the tower ring
     --together with a system of multilinear parameters
     --(degree = {1,..,1})
     --for the whole product.
     --The length of the sop is 
     --numgens A + sum D, 1 more than 
     --the projective dimension of the whole product.
     --The sop is formed from the symmetric functions
     --using the functions "partitions" above. (It could
     --also be done putting an appropriate matrix
     --in the next routine.)
     S := A;
     x := local x;
     SList := apply (#D, i->S = S[x_(i,0)..x_(i,D_i)]);
     SList = prepend(A,SList);
     SS := last SList;
     dimList := prepend(numgens A-1, D);
        --now make the parameters
     params := matrix{
	  for k from 0 to sum dimList list(
     P := partitions(k,dimList);
     sum(P, p -> product(#dimList, i->sub(SList_i_(p_i), SS))
	  )
                                           ) 
                     };
     (SS,params)
     )
///
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
notify=true
loadPackage("BGG", Reload =>true)
load "examples2.m2"
dL = {1,1}
dLPlus = dL +splice {#dL:1}
A = kk[vars (0..product(dLPlus)-1)]
L = projectiveProduct (A,dL,Sparse =>false)
betti L_1
transpose L_1

dimList = {1,1}
dimList = {2}
dimList = {0,1}
A = kk[a,b]
L = projectiveProduct (A,dimList)
betti L_1
///

projectiveProduct(Matrix, List) := opts -> (M,D) -> (
     --Takes a list D of dimensions
     --and makes the appropriate product of 
     --projective spaces over a base ring A = ring M, as a tower ring.
     --Returns the tower ring
     --together with a system of q linear combinations of
     --the 1...1 forms specified by M, which must
     --have product(D_0+1, .. ,D_r+1) rows (and q columns),
     A := ring M;
     S := A;
     x := local x;
     SList := apply (#D, i->S = S[x_(i,0)..x_(i,D_i)]);
     SList = prepend(A,SList);
     SS := last SList;
   --now make the parameters
     if numrows M != product(D, d->1+d) then
	       error("M has the wrong number of rows");
     N := gens trim product apply(#D, i->
	  promote(ideal vars SList_(i+1), SS));
     params := map(SS^1, SS^{numcols M:{-1,-1,-1}}, N*M);
     (SS,params)
     )
///
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
notify=true
loadPackage("BGG", Reload =>true)
load "examples2.m2"
dL = {1,1}
q = 3

t = product(dL, i->1+i)
A = kk[vars(0..q*t-1)]

M = genericMatrix(A,A_0,t,q)
L = projectiveProduct (M,dL)
betti L_1
numcols M
///

--Now given a degree list degList, form the corresponding
--product of projective spaces and the Koszul complex over
--it, and take the direct image to get a pure resolution.

pureResolution(Ring, List) := opts -> (A, degListOrig) -> (
     n := #degListOrig - 1;
     --normalize the degList to make the first entry zero:
     degList := apply(n+1, i-> degListOrig_i - degListOrig_0);
          
     --check the conditions for a pure resolution:
     if numgens A < n then 
        error("number of vars should be >= (length of list)-1");
     for i from 1 to n do (
	  if degList_i <= degList_(i-1) then 
	      error("list must be strictly increasing")
	      );

     --get ready to form the product of projective spaces
     dimList1 := apply(#degList-1, i->degList_(i+1)-degList_i-1);
     --dimList1 = {m_1..m_n} in the notation of our paper.
     degList1 := degList_{0..n-1};
     --degList1 = {0,d_1,..,d_(n-1)} in the notation of our paper.
     
     --Now drop the terms where m_i = 0
     jumpList := positions(dimList1, i-> i>0);
     dimList := dimList1_jumpList;
     
     twists := {0}|degList1_jumpList;
     --the leading zero corresponds to the base ring A.
     --Note that degList1 already begins with a zero corresponding
     --to the normalized degreeList_0.

     (S,params) := projectiveProduct(A, dimList, Sparse=>opts.Sparse);
     K := S^{reverse twists}**koszul(params);
--error();
     while ring K =!= A do (
	  K = directImageComplex K;
	  S = ring K);
     
     --now restore the zero-th twist of degListOrig
     A^{-degListOrig_0} ** K
     )

pureResolution(Matrix, List) := opts -> (M, degListOrig) -> (
     A := ring M;
     n := #degListOrig - 1;
     --normalize the degList to make the first entry zero:
     degList := apply(n+1, i-> degListOrig_i - degListOrig_0);
          
     for i from 1 to n do (
	  if degList_i <= degList_(i-1) then 
	      error("list must be strictly increasing")
	      );

     --get ready to form the product of projective spaces
     dimList1 := apply(#degList-1, i->degList_(i+1)-degList_i-1);
     --dimList1 = {m_1..m_n} in the notation of our paper.
     degList1 := degList_{0..n-1};
     --degList1 = {0,d_1,..,d_(n-1)} in the notation of our paper.
     
     --Now drop the terms where m_i = 0
     jumpList := positions(dimList1, i-> i>0);
     dimList := dimList1_jumpList;
     --check for input errors
     if numrows M != product(dimList, d->d+1) then
     	  error("M has the wrong number of rows");
     
     twists := {0}|degList1_jumpList;
     --the leading zero corresponds to the base ring A.
     --Note that degList1 already begins with a zero corresponding
     --to the normalized degreeList_0.

     --now set up the direct image computation
     (S,params) := projectiveProduct(M, dimList);
     K := S^{reverse twists}**koszul(params);
     while ring K =!= A do (
	  K = directImageComplex K;
	  S = ring K);
     
     --now restore the zero-th twist of degListOrig
     A^{-degListOrig_0} ** K
     )

pureResolution(ZZ, List) := (p, degList) -> (
--a version with the sparse system of parameters, giving
--just the characteristic and letting the program supply the
--ground ring.(Produces module of finite length with the given
--pure resolution type.)
     a := local a;
     A := ZZ/p[a_0..a_(#degList-2)];
     pureResolution(A, degList, Sparse => opts.Sparse)
     )


pureResolution(ZZ,ZZ,List):= opts -> (p, q, degList) -> (
     --A version with a generic system of q parameters.     
     --p will be the characteristic, q the number of parameters
     --(the codimension of support, 
     --at least when q is large enough.)
     
     --first compute the number of variables needed:
     dimList1 := apply(#degList-1, i->degList_(i+1)-degList_i-1);
     --dimList1 = {m_1..m_n} in the notation of our paper.
     --Now drop the terms where m_i = 0
     jumpList := positions(dimList1, i-> i>0);
     dL := dimList1_jumpList;
     t = product(dL, i->1+i);
     a := local a;
     A := ZZ/p[a_0..a_(q*t-1)];
     M := genericMatrix(A,A_0,t,q);
     pureResolution(M, degList)
     )
end

restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
loadPackage("BGG", Reload =>true)
debug BGG
load "examples2.m2"

B = kk[A_0..A_15]
MM = genericMatrix(B,B_0, 4,4)
betti(F = pureResolution(11, {0,2,4}))
betti(F = pureResolution(MM, {0,2,4}))
betti res coker F.dd_1
betti(F = pureResolution(11,5, {0,2,4}))


betti (G = res coker F.dd_1)
F.dd_1
G.dd_1
prune (homology F)_1

transpose (projectiveProduct(kk[a,b], {1,1}))_1
transpose (projectiveProduct(kk[a,b,c,d], {1,1}))_1
transpose (projectiveProduct(kk[a,b,c,d], {1,1}))_1

A = kk[a,b,c,d]
betti (F= pureResolution(A, {0,2,3}))
betti (F= pureResolution(11, {0,2,3}))
betti(F = pureResolution(kk[a,b], {0,2,4}))
F.dd_1
prune (homology F)_1

D = degList = {0,1,3,4,6,7}
time betti (F = pureResolution(11, D)) -- 6.6 sec







--the following code is not actually used
analyzeProductOfProjectiveSpaces = method()
analyzeProductOfProjectiveSpaces (Ring):= S -> (
     -- given an iterated tower ring S = A[x_(0,0)..x_0,n1][...]
     --representing a product of projective spaces over A, say
     --P^(e_0) x P^(e_1) x ... x P^(e_m), this returns the list
     --of e_i 
     K := ultimate(coefficientRing, S);
     T := S;
     eList := {};
     while T =!= K do (
	  eList = append(eList, numgens T - 1);
	  T = coefficientRing T);
     reverse eList)
///
KK=ZZ/101
A = KK[x_1..x_4]
B = A[a,b]
C = B[s,t]
D = C[u,v]
eList = analyzeProductOfProjectiveSpaces  D
///

productIndices = method()
productIndices List := D ->(
     if D == {} then return {};
     if D_0 == 0 then return {};
     if #D == 1 then return apply(D_0, i->{i});
     prod1 := productIndices drop(D,1);
     flatten apply(D_0, i-> apply(prod1, I->prepend(i,I)))
     )
///
restart
path = prepend( "/Users/david/src/Colorado-2010/PushForward",path)
notify=true
loadPackage("BGG", Reload =>true)
load "examples2.m2"
productIndices {}
productIndices {0}
productIndices {2}
productIndices {2,2}
productIndices {2,2,2}
productIndices{0,2}
productIndices{2,0}
///
