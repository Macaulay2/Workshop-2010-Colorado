restart
needsPackage "Schubert2"
--To do:
-- -In incidenceCorrespondence:
--   -Allow user to input {a,b,n} and a base variety (to default to OO_X^n as bundle)
--   -Add a VariableNames option for the Intermediate
--   -Extend to arbitrary flag bundles
-- -Other
--   -Implement building simple correspondences, given by two abstract varieties
--      and a cycle class in a variety dominating both

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

Correspondence = new Type of MutableHashTable
IncidenceCorrespondence = new Type of Correspondence
IncidenceCorrespondence.synonym = "incidence correspondence"
SimpleCorrespondence = new Type of Correspondence
SimpleCorrespondence.synonym = "simple correspondence"
globalAssignment Correspondence
toString Correspondence := net Correspondence := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "a correspondence")
Correspondence#{Standard,AfterPrint} = X -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "a correspondence from " << X.Source << " to " << X.Target << endl;
     )
toString IncidenceCorrespondence := net IncidenceCorrespondence := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "an incidence correspondence")
IncidenceCorrespondence#{Standard,AfterPrint} = X -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "an incidence correspondence from " << X.Source << " to " << X.Target << endl;
     )

Correspondence _* := Function => c -> c.SourceToTarget
Correspondence ^* := Function => c -> c.TargetToSource
source Correspondence := AbstractVariety => c -> c.Source
target Correspondence := AbstractVariety => c -> c.Target
transpose Correspondence := Correspondence => c -> (
     new Correspondence from {
	  Source => target c,
	  Target => source c,
	  SourceToTarget => c.TargetToSource,
	  TargetToSource => c.SourceToTarget})
transpose IncidenceCorrespondence := IncidenceCorrespondence => c -> (
     new IncidenceCorrespondence from {
	  Source => target c,
	  Target => source c,
	  SourceToTarget => c.TargetToSource,
	  TargetToSource => c.SourceToTarget,
	  Intermediate => c.Intermediate,
	  IntermediateToSource => c.IntermediateToTarget,
	  IntermediateToTarget => c.IntermediateToSource})
intermediates = method()
intermediates IncidenceCorrespondence := AbstractVariety => c -> (
     c.Intermediate, c.IntermediateToSource, c.IntermediateToTarget)
intermediates SimpleCorrespondence := AbstractVariety => c -> c.Intermediate

Correspondence * Correspondence := Correspondence => (X,Y) -> (
     new Correspondence from {
	  Source => source Y,
	  Target => target X,
	  SourceToTarget => X.SourceToTarget @@ Y.SourceToTarget,
	  TargetToSource => Y.TargetToSource @@ X.TargetToSource})

incidenceCorrespondence = method(TypicalValue => IncidenceCorrespondence)
incidenceCorrespondence(List) := L -> (
     if not #L == 3 then error "expected a list of length 3";
     if not all(L, i-> instance(i,ZZ) and i > 0) then "expected a list of positive integers";
     if not L#0 < L#2 and L#1 < L#2 then "expected last list element to be largest";
     G1 := flagBundle({L#0,L#2 - L#0});
     G2 := flagBundle({L#1,L#2 - L#1});
     incidenceCorrespondence(G1,G2))
incidenceCorrespondence(List,AbstractSheaf) := (L,B) -> (
     if not #L == 2 then error "expected a list of length 2";
     if not all(L, i-> instance(i,ZZ) and i > 0) then "expected a list of positive integers";
     n := rank B;
     if not all(L, i-> n > i) then "expected a list of integers smaller than rank of bundle";
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
     a := rank s1;
     b := rank s2;
     if a > b then transpose incidenceCorrespondence(G2,G1) else (
	 if not lift(chern(s1+q1),B) == lift(chern(s2+q2),B) then error "expected Grassmannians of same bundle";
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
	 pushforward ZZ := pushforward QQ := r -> promote(r,R2);
	 pushforward R1 := c -> (pfmap (k1 c));
	 pushforward AbstractSheaf := E -> (
	      abstractSheaf(I2,Rank => rank E, ChernClass => pushforward chern E));
	 M2 := matrix {apply(gens R2', e -> (
	      sum(n-b+1, i -> sum(b-a+1, j-> (
		   coefficient(k2(chern(i,Q2)*chern(j,QS2)), e)*chern(i,QQ1)*chern(j,SQ1))))))};
	 pbmap := map(R1,R2',M2);
	 pullback := method();
	 pullback ZZ := pullback QQ := r -> promote(r,R1);
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
	 sourcetotarget := method();
	 sourcetotarget ZZ := sourcetotarget QQ :=
	 sourcetotarget A1 := sourcetotarget AbstractSheaf := c -> (
	      g_* (iso_* (f^* c)));
	 targettosource := method();
	 targettosource ZZ := targettosource QQ :=
	 targettosource A1 := targettosource AbstractSheaf := c -> (
	      f_* (iso^* (g^* c)));
	 rez := new IncidenceCorrespondence from {
	      Source => G1,
	      Target => G2,
	      Intermediate => I1,
	      IntermediateToSource => f,
	      IntermediateToTarget => g * iso,
	      SourceToTarget => sourcetotarget,
	      TargetToSource => targettosource};
	 rez))

doc ///
  Key
    incidenceCorrespondence
  Headline
    Build containment correspondence between two Grassmannians
  Usage
    incidenceCorrespondence(G1,G2)
  Inputs
    G1:FlagBundle
      a Grassmannian of $a$-dimensional subbundles of a vector bundle $E$
    G2:FlagBundle
      another Grassmannian of $b$-dimensional subbundles of $E$, with $a<b$.
  Outputs
    :IncidenceCorrespondence
///

doc ///
  Key
    intermediates
    (intermediates, IncidenceCorrespondence)
  Usage
    intermediates IC
  Inputs
    IC:IncidenceCorrespondence
  Outputs
    :
      a triple $(I,f,g)$ where $I$ is the AbstractVariety mediating the Correspondence, $f$ is
      the AbstractVarietyMap from $I$ to the source of IC, and $g$ is the AbstractVarietyMap
      from $I$ to the target of IC.
///
end

--Test code 1
restart
load "incidencecor2.m2"
help incidenceCorrespondence
help intermediates
G1 = flagBundle({1,3},VariableNames => K)
G2 = flagBundle({2,2},VariableNames => L)
IC = incidenceCorrespondence(G1,G2)
intermediates IC
source IC
target IC
f = IC.IntermediateToSource
g = IC.IntermediateToTarget
c = 3*(chern(1,G1.Bundles#0))^2 -- 3 times the class of a line in PP3
g_* f^* c -- should be 3sigma_1 = 3L_(2,1)
st = IC.SourceToTarget
st c
IC_* c
IC_* 1
IC^* 1

c2 = schubertCycle({1,0},G2)
f_* g^* c2 -- should be 0 because of dimension considerations
ts = IC.TargetToSource
ts c2
f_* g^* ((c2)^2)
ts ((c2)^2)

T = G2.TangentBundle
IC^* T
T = G1.TangentBundle
IC_* T

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

--Test code 4:Composition
restart
load "incidencecor2.m2"
G1 = flagBundle({1,3},VariableNames => K)
G2 = flagBundle({2,2},VariableNames => M)
G3 = flagBundle({3,1},VariableNames => L)
I1 = incidenceCorrespondence(G1,G2)
I2 = incidenceCorrespondence(G2,G3)
I3 = I2 * I1
T = G1.TangentBundle
I3_* T

I1' = transpose I1
c = (chern(1,G2.Bundles#0))*(chern(2,G2.Bundles#1))
I1'_* c
