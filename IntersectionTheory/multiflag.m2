--given base variety X, bundles E_1,..,E_n, and sequences 
--{a_(1,1),..,a_(1,k_1)}, ... , {a_(n,1),..,a_(n,k_n)},
--produce the flag variety given by

multiFlag = method()
multiFlag(List,List) := (bundleRanks, bundles) -> (
     K := local K;
     if not #bundleRanks == #bundles then error "expected same number of bundles as lists of ranks";
     if not all(bundleRanks, l -> all(l, r -> instance(r,ZZ) and r>=0)) then error "expected bundles ranks to be positive integers";
     X := variety bundles#0;
     if not all(bundles, b -> (variety b) === X) then error "expected all bundles over same base";
     n := #bundleRanks;
     for i from 0 to n-1 do (
	  if not sum(bundleRanks#i) == rank bundles#i then error "expected rank of bundle to equal sum of bundle ranks");
     varNames = apply(0 .. n-1, i -> apply(1 .. #(bundleRanks#i), bundleRanks#i, (j,r) ->(
		    apply(toList(1..r), k -> new IndexedVariable from {K,(i+1,j,k)}))));
     --i -> base bundle, j -> bundle in flag from base bundle, k -> chern class
     Ord := GRevLex;
     dgs := splice flatten apply(bundleRanks, l -> apply(l, r-> 1 .. r));
     S := intersectionRing X;
     mo := flatten apply(bundleRanks, l -> apply(l, r -> Ord => r));
     hft := {1};
     U := S(monoid [flatten flatten varNames, Degrees => dgs, MonomialOrder => mo, Join => false, Heft => hft, DegreeRank => 1]);
     A := U; F := identity;
     chclasses := apply(varNames, l->apply(l, x -> F (1_U + sum(x, v-> U_v))));
     rlns := apply(chclasses, bundles, (c,b) -> product c - F promote(chern b, U));
     rlns = flatten apply(rlns, r -> sum @@ last \ sort pairs partition(degree,terms(QQ,r)));
     rlns = ideal matrix(U,{rlns});
     HR := degreesRing hft;
     T := HR_0;
     hilbertSeriesHint := product for i from 0 to n-1 list (
	  k := sum (bundleRanks#i);
	  product for j from 1 to k list 1 - T^j);
     if heft S =!= null and degreesRing S === HR then (
         gb(rlns, Hilbert => hilbertSeriesHint * numerator hilbertSeries S));
     B := A/rlns;
     C := B; H := identity;
     d := dim X + sum(bundleRanks, l-> (
	       sum(0 .. #l-1, i-> sum(0 .. i-1, j-> l#i * l#j))));
     MF = C.Variety = abstractVariety(d,C);
     MF.Base = X;
     MF.Bundles = apply(0 .. n-1, l -> (
	         	       apply(0 .. #(bundleRanks#l)-1, i -> (
			 bdl := abstractSheaf(MF, Rank => bundleRanks#l#i, ChernClass => H promote(chclasses#l#i,B));
			 bdl))));
     pullback := method();
     pushforward := method();
     pullback ZZ := pullback QQ := r -> promote(r,C);
     pullback S := r -> H promote(F promote(r,U), B);
     sec := if n === 0 then 1_C else (
	  product(0 .. n-1, l-> (
		    if #(bundleRanks#l) === 0 then 1_C else (
		         product(1 .. #(bundleRanks#l)-1, i -> promote((ctop MF.Bundles#l#i)^(sum(i, j -> bundleRanks#l#j)),B))))));
     pushforward C := r -> coefficient(sec,r);
     pullback AbstractSheaf := E -> (
	  if variety E =!= X then error "pullback-variety mismatch";
	  abstractSheaf(FV,Rank => rank E, ChernClass => pullback chern E));
     p := new AbstractVarietyMap from {
	  global target => X,
	  global source => MF,
	  SectionClass => sec,
	  PushForward => pushforward,
	  PullBack => pullback
	  };
     MF.StructureMap = p;
     MF
     )


map(FlagBundle,FlagBundle) := opts -> (B,A) -> (
     if not A.Base === B.Base then error "expected flag bundles over same base";
     S := intersectionRing B.Base;
     Arks := A.BundleRanks;
     Brks := B.BundleRanks;
     if not sum(Arks) == sum(Brks) then error "expected flag bundles of same rank";
     if not lift(chern(sum(toList A.Bundles)),S) == lift(chern(sum(toList B.Bundles)),S) then error "expected flag bundles of same bundle";
     reached := 0;
     Apart := for i from 0 to #Brks - 1 list (
	  startpoint := reached;
	  currentsum := 0;
	  while currentsum < Brks#i and reached < #Arks do (
	       (currentsum, reached) = (currentsum + Arks#reached, reached+1));
	  if not currentsum == Brks #i then error "rank sequences incommensurable" else (take(Arks,{startpoint,reached-1}),reached-1));
     --first elt of Apart#i is the list of A-ranks used to make Brks#i,
     --second element is the index of the last A-rank used to make Brks#i
     --so, for example, if Arks = {1,2,2,1,3}, Brks = {3,3,3}, then
     --Apart = {({1,2},1),({2,1},3),({3},4)} 
     MF := multiFlag(first \ Apart,toList B.Bundles);
     RA := intersectionRing A;
     RB := intersectionRing B;
     RMF := intersectionRing MF;
     (RMF',k1) = flattenRing(RMF,CoefficientRing=>RB);
     Bimages := flatten for l in Apart list (
	  rks := l#0;
	  lastbund := l#1;
	  total := sum for i from 0 to #rks - 1 list A.Bundles#(lastbund-i);
	  for r from 1 to rank total list chern(r,total));
     M1 := matrix {gens RA | Bimages};
     f1 := map(RA,RMF',M1);
     mftoA := method();
     mftoA ZZ := mftoA QQ := r -> promote(r,RA);
     mftoA RMF := c -> f1(k1 c);
     mftoA AbstractSheaf := E -> (
	  abstractSheaf(A, Rank => rank E, ChernClass => mftoA chern E));
     Atomf := method();
     Atomf ZZ := Atomf QQ := r -> promote(r,RMF);
     Atomf RA := c -> ((map(RMF,RA,gens RMF)) c);
     Atomf AbstractSheaf := E -> (
	  abstractSheaf(MF, Rank => rank E, ChernClass => Atomf chern E));
     iso := new AbstractVarietyMap from {
	  global source => A,
	  global target => MF,
	  SectionClass => 1_RA,
	  PushForward => Atomf,
	  PullBack => mftoA};
     mftoB := MF / B;
     mftoB * iso
     )
	  
	  
end
------Junk code used in working out the above
restart
bundleRanks = {2,2,3,4}
n = #bundleRanks
d = sum(n, i -> sum(i+1 .. n-1, j -> bundleRanks#i * bundleRanks#j))
d' = sum(0 .. n-1, i-> sum(0 .. i-1, j-> bundleRanks#i * bundleRanks#j))

---Tests for multiFlag
restart
loadPackage "Schubert2"
load "multiflag.m2"
X = flagBundle({3,3,3})
(A,B,C) = X.Bundles
bundles = {A,B,C}
bundleRanks = {{1,2},{2,1},{3}}
MF = multiFlag({{1,2},{2,1},{3}},{A,B,C})
MF.Bundles
f = MF.StructureMap
g = X / point
c1 = (chern(2,MF.Bundles#0#1))
c2 = (chern(2,MF.Bundles#1#0))^3
c3 = (chern(1,MF.Bundles#1#1))^5
c4 = (chern(3,MF.Bundles#2#0))^6
g_* f_* (c1*c2*c3*c4) -- pushforward of relative point, should be 1

--More junk code
RMF = intersectionRing MF
L1 = gens intersectionRing MF
L2 = flatten flatten for b in MF.Bundles list (
     for bund in b list (
	  for i from 1 to (rank bund) list chern(i,bund)))
(RMF', kMF) = flattenRing(RMF,CoefficientRing=>QQ)
B1 = matrix {gens RMF'}
numgens RMF'
S = intersectionRing X
numgens S
gens S
B2 = matrix {kMF \ (L2 | gens S)}
#(flatten toList entries oo)
--Want a map from RMF' to Y, given by taking chern classes of bundles to corresponding chern
--classes, and chern classes in base X to the correct products in chern classes in Y
--In this case, matrix should be:
--For each bundle on X, write the chern classes of the corresponding total bundle on Y.
--For each bundle on the multiflag just send it to the corresponding Y-Bundle
Apart = {({1,2},1),({2,1},3),({3},4)}
for l in Apart list (
     rks := l#0;
     lastbund := l#1;
     total := sum for i from 0 to #rks - 1 list Y.Bundles#(lastbund - i);
     for r from 1 to rank total list chern(r,total))
flatten oo      
#oo
#L2
Y = flagBundle({1,2,2,1,3})
RY = intersectionRing Y
gens RY
flatten for bund in Y.Bundles list for i from 1 to rank bund list chern (i,bund)

----Begin test code for forgetfulMap
restart
loadPackage "Schubert2"
load "multiflag.m2"
X = flagBundle({3,3,3})
Y = flagBundle({1,2,2,1,3})
f = map(X,Y)
relpt = chern(2,Y.Bundles#1)*((chern(1,Y.Bundles#3))^2)
f_* relpt --pushforward of class of a relative point, should be 1
f^* chern(X.Bundles#2)
f_* (relpt * (f^* chern(2,X.Bundles#2))) -- f_*(relpt*f^*(a)) = a, in this case H_(3,2)
assert (f_* (relpt * (f^* chern(2,X.Bundles#2))) == chern(2,X.Bundles#2))

G = flagBundle({4,3})
(S,Q) = G.Bundles
Y = flagBundle({1,3,3}) --should be same as P(S)
g = map(G,Y)
z = -chern(1,Y.Bundles#0) -- the class of O(1) considering Y as P(S)
g_* (z^3) --0th segre class of S, should be 1
g_* (z^4) --1st segre class of S (=1st chern class of Q), should be H_(2,1)
g_* (z^5) --2nd segre class of S, should be H_(2,2)
--next examples check push-pull for segre class intersections:
g_* (z^3 * (g^* chern(1,G.Bundles#0))) -- should be H_(1,1) = -H_(2,1)
g_* (z^4 * (g^* chern(1,G.Bundles#0))) -- should be -H_(2,1)^2

--now testing with a base parameter
A = base n
G = flagBundle({4,3},A)
(S,Q) = G.Bundles
Y = flagBundle({1,3,3},A) --should be same as P(S)
g = map(G,Y)
z = -chern(1,Y.Bundles#0) -- the class of O(-1) considering Y as P(S)
AG = intersectionRing G
g_* (z^3) --0th segre class of S, should be 1
g_* (z^4) --1st segre class of S (=1st chern class of Q), should be H_(2,1)
g_* (z^5) --2nd segre class of S, should be H_(2,2)
--next examples check push-pull for segre class intersections:
g_* (z^3 * (g^* chern(1,G.Bundles#0))) -- should be H_(1,1) = -H_(2,1)
g_* (z^4 * (g^* chern(1,G.Bundles#0))) -- should be -H_(2,1)^2
--a few examples using base parameter:
z = -chern(1,Y.Bundles#0)*n -- the class of O(-1) considering Y as P(S)
g_* (z^3) --n^3 
g_* (z^4) --n^4*H_(2,1)
g_* (z^5) --n^5*H_(2,2)
g_* (z^3 * (g^* (n*chern(1,G.Bundles#0)))) -- -n^4*H_(2,1)
