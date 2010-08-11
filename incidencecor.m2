restart
needsPackage "Schubert2"
--To do:
-- -Allow user to input {a,b,n} and a base variety
-- -Add a VariableNames option for the Intermediate
-- -Extend to arbitrary flag bundles

IncidenceCorrespondence = new Type of MutableHashTable

incidenceCorrespondence = method(TypicalValue => IncidenceCorrespondence)
incidenceCorrespondence(List) := L -> (
     if not #L == 3 then error "expected a list of length 3";
     if not all(L, i-> instance(i,ZZ) and i > 0) then "expected a list of positive integers";
     if not L#0 < L#1 and L#1 < L#2 then "expected a list of strictly increasing integers";
     G1 := flagBundle({L#0,L#2 - L#0});
     G2 := flagBundle({L#1,L#2 - L#1});
     incidenceCorrespondence(G1,G2))
incidenceCorrespondence(List,AbstractSheaf) := (L,B) -> (
     if not #L == 2 then error "expected a list of length 2";
     if not all(L, i-> instance(i,ZZ) and i > 0) then "expected a list of positive integers";
     if not L#0 < L#1 then "expected a list of strictly increasing integers";
     n := rank B;
     G1 := flagBundle({L#0,n - L#0},B);
     G2 := flagBundle({L#1,n - L#1},B);
     incidenceCorrespondence(G1,G2))
incidenceCorrespondence(FlagBundle,FlagBundle) := (G1,G2) -> (
     if not G1.Base === G2.Base then error "expected FlagBundles over same base";
     B := intersectionRing G1.Base;
     if not (#G1.Bundles == 2 and #G2.Bundles == 2) then error "expected two Grassmannians";
     n := sum G1.BundleRanks;
     if not n == (sum G2.BundleRanks) then error "expected Grassmannians of same bundle";
     (s1,q1) := G1.Bundles;
     (s2,q2) := G2.Bundles;
     if not lift(chern(s1+q1),B) == lift(chern(s2+q2),B) then error "expected Grassmannians of same bundle";
     a := rank s1;
     b := rank s2;
     if not a < b then error "currently require first argument to be Grassmannian of smaller subspaces";
     I1 := flagBundle({b-a, n-b},q1);
     I2 := flagBundle({a, b-a},s2);
     f := I1/G1;
     g := I2/G2;
     Q1 := f^* q1;
     Q2 := g^* q2;
     SQ1 := I1.Bundles#0;
     QQ1 := I1.Bundles#1;
     QS2 := I2.Bundles#1;
     Qa2 := Q2 + QS2; -- corresponds to quotients of rank n-a in I2
     R1 := intersectionRing I1;
     R2 := intersectionRing I2;
     (R1', k1) := flattenRing(R1,CoefficientRing => B);
     (R2', k2) := flattenRing(R2,CoefficientRing => B);
     M1 := matrix {apply(gens R1', e -> (
	  sum(n-a+1, i -> sum(n-b+1, j-> (
	       coefficient(k1(chern(i,Q1)*chern(j,QQ1)), e)*chern(i,Qa2)*chern(j,Q2))))))};
     pfmap := map(R2,R1',M1);
     pushforward := method();
     pushforward R1 := c -> (pfmap (k1 c));
     pushforward AbstractSheaf := E -> (
	  abstractSheaf(I2,Rank => rank E, ChernClass => pushforward chern E));
     M2 := matrix {apply(gens R2', e -> (
	  sum(n-b+1, i -> sum(b-a+1, j-> (
	       coefficient(k2(chern(i,Q2)*chern(j,QS2)), e)*chern(i,QQ1)*chern(j,SQ1))))))};
     pbmap := map(R1,R2',M2);
     pullback := method();
     pullback R2 := c -> (pbmap (k2 c));
     pullback AbstractSheaf := E -> (
	  abstractSheaf(I1,Rank => rank E, ChernClass => pullback chern E));
     iso := new AbstractVarietyMap from {
	  global source => I1,
	  global target => I2,
	  SectionClass => 1_R1,
	  PushForward => pushforward,
	  PullBack => pullback};
     A1 := intersectionRing G1;
     A2 := intersectionRing G2;
     sourcetotarget = method();
     sourcetotarget A1 := c -> (
	  g_* (iso_* (f^* c)));
     targettosource = method();
     targettosource A2 := c -> (
	  f_* (iso^* (g^* c)));
     rez := new IncidenceCorrespondence from {
	  Source => G1,
	  Target => G2,
	  Intermediate => I1,
	  IntermediateToSource => f,
	  IntermediateToTarget => g * iso,
	  SourceToTarget => sourcetotarget,
	  TargetToSource => targettosource};
     rez)
end

--Test code 1
restart
load "incidencecor2.m2"
G1 = flagBundle({1,3},VariableNames => K)
G2 = flagBundle({2,2},VariableNames => L)
IC = incidenceCorrespondence(G1,G2)
f = IC.IntermediateToSource
g = IC.IntermediateToTarget
c = 3*(chern(1,G1.Bundles#0))^2 -- 3 times the class of a line in PP3
g_* f^* c -- should be 3sigma_1 = 3L_(2,1)
st = IC.SourceToTarget
st c

c2 = schubertCycle({1,0},G2)
f_* g^* c2 -- should be 0 because of dimension considerations
ts = IC.TargetToSource
ts c2
f_* g^* ((c2)^2)
ts ((c2)^2)

T = G2.TangentBundle
f_* g^* T

IC = incidenceCorrespondence({1,2,4})
G1 = IC.Source
G2 = IC.Target
f = IC.IntermediateToSource
g = IC.IntermediateToTarget
c = 3*(chern(1,G1.Bundles#0))^2
g_* f^* c

--Test code 2
restart
load "incidencecor2.m2"
B = flagBundle({1,4},VariableNames => M)
E = B.Bundles#1
G1 = flagBundle({1,3},E,VariableNames => K)
G2 = flagBundle({2,2},E,VariableNames => L)
IC = incidenceCorrespondence(G1,G2)
f = IC.IntermediateToSource
g = IC.IntermediateToTarget
c = 3*(chern(1,G1.Bundles#0))^2
g_* f^* c

T = G2.TangentBundle
f_* g^* T

B = flagBundle({1,4},VariableNames => M)
E = B.Bundles#1
IC = incidenceCorrespondence({1,2},E)
G1 = IC.Source
G2 = IC.Target
IC = incidenceCorrespondence(G1,G2)
f = IC.IntermediateToSource
g = IC.IntermediateToTarget
c = 3*(chern(1,G1.Bundles#0))^2
g_* f^* c

--Test code 3
restart
load "incidencecor2.m2"
G1 = flagBundle({2,3},VariableNames => K)
G2 = flagBundle({3,2},VariableNames => L)
IC = incidenceCorrespondence(G1,G2)
f = IC.IntermediateToSource
g = IC.IntermediateToTarget
c = 3*(chern(1,G1.Bundles#0))^3
g_* f^* c