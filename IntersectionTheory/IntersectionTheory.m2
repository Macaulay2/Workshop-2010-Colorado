-- -*- coding: utf-8 -*-
needsPackage "Schubert2"
needsPackage "SchurRings"

newPackage(
     "IntersectionTheory",
     Version => "0.1",
     Date => "July 20, 2010",
     Authors => {{Name => "Charley Crissman",
	       Email => "charleyc@math.berkeley.edu",
	       HomePage => "http://math.berkeley.edu/~charleyc/"}},
     Headline => "Examples to accompany the eponymous book by Eisenbud and Harris",
     DebuggingMode => true
     )

export {grassmannian, placeholderSchubertCycle, diagrams, placeholderToSchubertBasis,
     Correspondence, IncidenceCorrespondence, SimpleCorrespondence,
     incidenceCorrespondence, intermediates}

needsPackage "Schubert2"

protect Source
protect Target
protect SourceToTarget
protect TargetToSource
protect Intermediate
protect IntermediateToSource
protect IntermediateToTarget
protect htoschubert
protect schuberttoh
protect schubertring
protect intersectionmap

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
--is more efficient than using two forgetful maps because it creates one less intermediate object
incidenceCorrespondence(FlagBundle,FlagBundle) := (G1,G2) -> (
     if G1.Base =!= G2.Base then error "expected FlagBundles over same base";
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
	 Q1 := f^* q1; --rank n-a
	 S1 := f^* s1; --rank a
	 Q2 := g^* q2; --rank n-b
	 SQ1 := I1.Bundles#0; --rank b-a
	 QQ1 := I1.Bundles#1; --rank n-b
	 QS2 := I2.Bundles#1; --rank b-a
	 SS2 := I2.Bundles#0; --rank a
	 Qa2 := Q2 + QS2; -- corresponds to quotients of rank n-a in I2
	 Sb1 := SQ1 + S1; -- corresponds to subbundles of rank b in I1
	 R1 := intersectionRing I1;
	 R2 := intersectionRing I2;
	 (R1', k1) := flattenRing(R1,CoefficientRing => B);
	 (R2', k2) := flattenRing(R2,CoefficientRing => B);
	 --next line depends heavily on knowing the monomial basis of the
	 --intersectionRing of G(k,n)
	 --gens of R1' should be, in order:
	 --chern classes of subbundle on I1 (rank b-a, -> QS2)
	 m11 := for i from 1 to b-a list chern(i,QS2);
	 --chern classes of quotient bundle on I1 (rank n-b -> Q2)
	 m12 := for i from 1 to n-b list chern(i,Q2);
	 --chern classes of subbundle on G1 (rank a -> SS2)
	 m13 := for i from 1 to a list chern(i,SS2);
	 --chern classes of quotient bundle on G1 (rank n-a -> Qa2)
	 m14 := for i from 1 to n-a list chern(i,Qa2);
	 M1 := matrix {m11|m12|m13|m14};
	 pfmap := (map(R2,R1',M1)) * k1;
	 pushforward := method();
	 pushforward ZZ := pushforward QQ := r -> promote(r,R2);
	 pushforward R1 := c -> pfmap c;
	 pushforward AbstractSheaf := E -> (
	      abstractSheaf(I2,Rank => rank E, ChernClass => pushforward chern E));
         --gens of R2' should be, in order:
	 --chern classes of subbundle on I2 (rank a -> S1)
	 m21 := for i from 1 to a list chern(i,S1);
	 --chern classes of quotient bundle on I2 (rank b-a -> SQ1)
	 m22 := for i from 1 to b-a list chern(i,SQ1);
	 --chern classes of subbundle on G2 (rank b -> Sb1)
	 m23 := for i from 1 to b list chern(i,Sb1);
	 --chern classes of quotient bundle on G2 (rank n-b -> QQ1)
	 m24 := for i from 1 to n-b list chern(i,QQ1);
	 M2 := matrix {m21|m22|m23|m24};	 
	 pbmap := (map(R1,R2',M2)) * k2;
	 pullback := method();
	 pullback ZZ := pullback QQ := r -> promote(r,R1);
	 pullback R2 := c -> pbmap c;
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
	 targettosource A2 := targettosource AbstractSheaf := c -> (
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

grassmannian = method(TypicalValue => FlagBundle)
grassmannian(ZZ,ZZ) := (k,n) -> flagBundle({k,n-k}) --The grassmannian of k-dimensional subspaces of
                                                  --an n-dimensional space


placeholderSchubertCycle = method()
giambelli = (r,E,b) -> (
     p := matrix for i from 0 to r-1 list for j from 0 to r-1 list chern(b#i-i+j,E);
     if debugLevel > 15 then stderr << "giambelli : " << p << endl;
     det p
     )
placeholderSchubertCycle(List,FlagBundle) := (b,X) -> (
     if #X.BundleRanks != 2 then error "expected a Grassmannian";
     E := last X.Bundles;
     r := rank E;
     n := X.Rank;
     r' := n-r;
     if r' != #b then error("expected a list of length ", toString r');
     for i from 0 to r'-1 do (
	  bi := b#i;
	  if not instance(bi,ZZ) or bi < 0 then error "expected a list of non-negative integers";
	  if i>0 and not (b#(i-1) >= bi) then error "expected a decreasing list of integers";
	  if not (bi <= r) then error("expected a list of integers bounded by ",toString(r));
	  );
     giambelli(r',E,b))

diagrams = method()
diagrams(ZZ,ZZ) := (k,n) -> ( --diagrams {k>=a_1>=...>=a_n>=0}
     if n==1 then apply(k+1, i->{i})
     else flatten apply(k+1, i -> apply(diagrams(i,n-1), l -> flatten {i,l})))     
diagrams(ZZ,ZZ,ZZ) := (k,n,d) -> (--partitions of d of above form
     select(diagrams(k,n), i -> (sum(i) == d)))

placeholderToSchubertBasis = method()
placeholderToSchubertBasis(RingElement,FlagBundle) := (c,G) -> (
     if #G.BundleRanks != 2 then error "expected a Grassmannian";
     if not ring c === intersectionRing G then error "expected first input to be a ring element
     in the intersection ring of the second input";
     R := intersectionRing G;
     B := intersectionRing (G.Base);
     (k,q) := toSequence(G.BundleRanks);
     P := diagrams(q,k);
     M := apply(P, i-> placeholderSchubertCycle(i,G));
     E := flatten entries basis(R);
     local T';
     if R.cache.?htoschubert then T' = R.cache.htoschubert else (
	  T := transpose matrix apply (M, i -> apply(E, j-> coefficient(j,i))); --matrix converting from schu-basis 
                                                                 --to h-basis
	  T' = T^-1; --matrix converting from h-basis to s-basis
	  R.cache.schuberttoh = T;
	  R.cache.htoschubert = T');
     c2 := T'*(transpose matrix {apply (E, i-> coefficient(i,c))}); --c in the s-basis
     local S;
     if R.cache.?schubertring then S = R.cache.schubertring else (
	  s := local s;
	  S = B[apply(P, i-> s_i)]; --poly ring with generators <=> schubert basis elts
	  S.cache = new MutableHashTable;
	  S#{Standard,AfterPrint} = X -> (
	       << endl;
	       << concatenate(interpreterDepth:"o") << lineNumber << " : "
	       << "Schubert Basis of G(" << k << "," << k+q << ") over " << G.Base << endl;);
	  R.cache.schubertring = S;
	  S.cache.intersectionmap = map(R,S,M);
     	  S * S := (f,g) -> (
	       f1 := S.cache.intersectionmap(f);
	       g1 := S.cache.intersectionmap(g);
	       placeholderToSchubertBasis(f1*g1,G)
	       )
	  );
     rez := (vars S)*(lift(c2,B));
     rez_(0,0)
     )

beginDocumentation()

doc ///
  Key
    placeholderToSchubertBasis
    (placeholderToSchubertBasis,RingElement,FlagBundle)
  Headline
    Express cycles on G(k,n) in terms of the Schubert basis
  Usage
    placeholderToSchubertBasis(c,G)
  Inputs
    G:FlagBundle
      Any grassmannian (i.e. one-step flag variety) of $k$-dimensional subspaces of a rank-$n$
      bundle
    c:RingElement
      An element of the intersection ring of G
  Outputs
    :
      An element $c'$ of a polynomial ring $B[s_\lambda]$ where $B$ is the base ring of G and
      $\lambda$ runs over all diagrams in a $k\times n$ rectangle.  The element $c'$ is the
      representation of $c$ in terms of the Schubert basis of the intersection ring of G over B.
  Description
    Example
      A = flagBundle({3,3},VariableNames => H)
      S = A.Bundles#0
      G = flagBundle({1,2},S,VariableNames => K)
      c = H_(2,3)*((K_(2,1))^2) + H_(1,1)*K_(2,2)
      placeholderToSchubertBasis(c,G)
///

doc ///
  Key
    diagrams
    (diagrams,ZZ,ZZ)
  Headline
    Ferrers diagrams contained in a rectangle
  Usage
    diagrams(k,n)
  Inputs
    k:ZZ
      maximum size of each entry in diagram
    n:ZZ
      number of entries in diagram
  Outputs
    :
      a list of lists of integers $\{a_1, \dots, a_n\}$ such that 
      $k \geq a_1 \geq ... \geq a_n \geq 0$
///

doc ///
  Key
    (diagrams,ZZ,ZZ,ZZ)
  Headline
    Partitions contained in a rectangle
  Usage
    diagrams(k,n,d)
  Inputs
    k:ZZ
      maximum size of each entry in partitions
    n:ZZ
      number of entries in paritition
    d:ZZ
      number being partitioned
  Outputs
    :
      a list of lists of integers $\{a_1, \dots, a_n\}$ such that 
      $k \geq a_1 \geq ... \geq a_n \geq 0$ and
      $\sum_{i=1}^n a_i = d$
///

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

doc ///
  Key
    IntersectionTheory
  Headline
    Examples using M2 and Schubert2 to do intersection theory
  Description
    Text
      This package consists almost entirely of example code for the main text and exercises of the book
      '3264 & All That: Intersection Theory in Algebraic Geometry' by Eisenbud and Harris.  Most of the
      example code relies on the package @TO Schubert2@.  The information in this package is best
      accessed via the @TO help@ or @TO viewHelp@ commands.
      
      Conventions in effect throughout:
      
      -Blackboard bold is represented in code by doubling a letter, so for example {\tt G(2,4)} and 
      {\tt GG(1,3)} are both the Grassmannian of lines in ${\mathbb P}^3$.
  Subnodes
    :Chapter 4
    "Intersection Theory Section 4.1"
    "Intersection Theory Section 4.2"
    "Intersection Theory Section 4.3"
    :Chapter 5
    "Intersection Theory Section 5.2"
    "Intersection Theory Section 5.3"
    "Intersection Theory Section 5.4.1-2"
    "Intersection Theory Section 5.4.3"
    "Intersection Theory Section 5.4.4"
    :Chapter 7
    "Intersection Theory Chapter 7"
///

doc ///
  Key
    "Intersection Theory Section 4.1"
  Headline
    The coordinate ring of the Grassmannian
  Description
    Text
      Subsection 4.1.1
      
      We can use Macaulay2 to build the coordinate ring of $G(k,n)$
      using the Plucker embedding.  Exercise 4.4 is the simplest
      interesting case, $G(2,4) = {\mathbb G}(1,3)$.  We'll start there before
      writing more general code for this.
      
      Exercise 4.4:
    Example
      kk = ZZ/32003 --Our base field
      R = kk[x_1 .. x_8]
      M = genericMatrix(R,x_1,2,4) -- A generic 2x4 matrix in the x_i
      I = minors(2,M) -- The ideal of 2x2 minors of M
      P5 = kk[p_0 .. p_5] -- The coordinate ring of PP^5
      f = map(R,P5, gens I) -- The Plucker map for GG(1,3)
      J = saturate ker f -- The ideal of GG(1,3) in PP^3
    Text
      We see that the ideal $J$ of ${\mathbb G}(1,3)$ in ${\mathbb P}^5$ is indeed generated by the
      single relation given in the text.
      
      More generally, we can build $G(k,n)$ in its Plucker embedding for any $n$ and $k$:
    Example
      kk = ZZ/32003
      pluckerIdeal = (k,n) -> (
        assert (k <= n);
        N := k*n; --number of variables in our generic matrix
        R := kk[x_1 .. x_N];
        M := genericMatrix(R,x_1,k,n); --the generic k-by-n matrix
        s := binomial(n,k) - 1; --the dimension of PP(Wedge^k(kk^n))
        Ps = kk[p_0 .. p_s];
        f := map(R,Ps, gens minors(k,M)); --the Plucker map
        J = saturate ker f) --the kernel of the Plucker map is the ideal we want
      
    Text
      
      Now we can do Exercise 4.4 in one line:
    Example
      pluckerIdeal(2,4)
    Text
      The reader is invited to try running {\tt pluckerIdeal(4,7)}.  On our machine, this computation
      had not terminated after 15 minutes of runtime.
      
      We can do a little better by using the built-in function @TO Grassmannian@, which computes
      the Plucker ideal in a more efficient way:
    Example
      Grassmannian(1,4)
    Text
      The reader should try running {\tt Grassmannian(4,7)} (which runs very quickly) to see just
      how large this ideal is.  Running {\tt Grasmannian(4,10)}, on the other hand, is likely to
      never terminate.
      
      Given how large these rings are and how difficult it is to compute in them, we need to
      simplify our computational system if we want to get answers to harder questions.
            
      Subsection 4.1.3
      
      It is possible to use Macaulay2 to build the universal sub- and quotient- bundles of
      the Grassmannian using explicit equations.  However, as above, computations very
      quickly become intractable.  We need some simplifications if we hope to compute anything.
      Schubert2 makes two major simplifications that allow us to do intersection theory
      with computers:
      
      1) Varieties are replaced by their Chow rings
      2) Bundles are replaced by their (total) Chern classes (see Ch. 5)
      
      Here is Schubert code that will build the Grassmannian and its universal sub- and quotient
      bundles.
    Example
      grass = (k,n) -> flagBundle({k,n-k}) --In Schubert, we build Grassmannians as special cases
      G = grass(2,4) -- Our favorite GG(1,3)
      (S,Q) = G.Bundles -- S is the universal subbundle, Q is the universal quotient bundle
      S -- Schubert tells us that S is an abstract sheaf of rank 2
      Q -- And so is Q.
///

doc ///
  Key
    "Intersection Theory Section 4.2"
  Headline
    The Chow ring of GG(1,3)
  Description
    Text
      Subsection 4.2.2
      
      Schubert2 identifies ${\mathbb G}(1,3)$ with its Chow ring.  We can see this directly using the
      command {\tt intersectionRing}.
    Example
      G = flagBundle({2,2})
      intersectionRing G
    Text
      The generators $H_{i,j}$ of the above ring are defined by the formula $H_{i,j} = c_j(B_i)$ where
      $B_i$ is the {\tt i}-th bundle in the list G.Bundles (numbered starting with 1) and $c_j$ is the
      {\tt j}-th Chern class, defined in Ch. 5.  The relationship with the Schubert classes on
      ${\mathbb G}(1,3)$ is as follows:
      
      $H_{2,1} = \sigma_1$ @BR{}@ $H_{2,2} = \sigma_2$ @BR{}@ $H_{1,1} = -\sigma_1$ @BR{}@
      $H_{1,2} = \sigma_{1,1}$
      
      The Schubert classes can also be accessed directly using the {\tt placeholderSchubertCycle}
      command -- see Section 4.3 for details.
      
      As an example, we can compute $(\sigma_1)^2$:
    Example
      sigma_1 = H_(2,1)
      c = (sigma_1)^2
    Text
      Oops!  This just gave us $H_{2,1}^2$ back!  Schubert2 actually uses $\sigma_1^2$ and
      $\sigma_{1,1}$ as its "preferred basis" for the codimension-2 part of the Chow ring of
      ${\mathbb G}(1,3)$.  To convert to the Schubert basis, we use the function 
      @TO placeholderToSchubertBasis@:
    Example
      placeholderToSchubertBasis(c,G)
    Text
      We recover the formula of Theorem 4.13: $\sigma_1^2 = \sigma_2 + \sigma_{1,1}$.
      
      Subsection 4.2.4
      
      How many lines in ${\mathbb P}^3$ meet four general lines?
      
      After phrasing the problem in terms of Schubert calculus, this is easy to calculate both by hand
      and in Schubert2:
    Example
      sigma_1 = H_(2,1)
      integral (sigma_1)^4
    Text
      The command {\tt integral} here returns the degree of the zero-cycle $(\sigma_1)^4$, which is
      the number we want (namely, 2).

      Lines meeting a curve
      
      We can easily build a function which, given the degree $d$ of a space curve $C$, returns the
      cycle of lines in ${\mathbb P}^3$ meeting $C$:
    Example
      sigma_1 = H_(2,1)
      linesMeetingCurve = d -> d*sigma_1
    Text
      And now we can calculate, for example, how many lines meet four general conics:
    Example
      integral (linesMeetingCurve(2))^4
    Text
      But we really want to answer the question once and for all: how many lines meet four general
      curves of degree $d$?  To do this, we use the @TO base@ command, which allows us auxiliary
      parameters:
    Example
      S = base d --Our base variety, with one "auxiliary parameter" d
      G' = flagBundle({2,2},S,VariableNames => K) --GG(1,3) with our extra parameter
      intersectionRing G' --note the additional parameter d
      sigma_1 = K_(2,1)
      linesmeetingcurve = d*sigma_1
      integral linesmeetingcurve^4
    Text
      And we get back the answer $2d^4$, solving the problem once and for all.
    
      Chords to a Space Curve
      
      For each $d$ and $g$ we build the cycle in ${\mathbb G}(1,3)$ of lines secant
      to a general curve of degree d and genus g:  
    Example
      S = base(g,d') --We use d' to avoid the d from the last example
      G'' = flagBundle({2,2},S,VariableNames => L)
      sigma_2 = L_(2,2)
      sigma_(1,1) = L_(1,2)
      cycleofchords = ((d'-1)*(d'-2)/2 - g)*sigma_2 + (d'*(d'-1)/2)*sigma_(1,1)
    Text
      The keynote question was: how many lines are secant to two general twisted cubics?  But
      we can do better, and answer the question: how many lines are secant to two general curves
      of degree $d$ and genus $d$?
    Example
      chordstotwocurves = integral cycleofchords^2
    Text
      Now if we want to answer our specific question, we just subsitute in the desired values
      for $d$ and $g$:
    Example
      sub(chordstotwocurves, {d' => 3, g => 0/1})
    Text
      WARNING: because of some ugly M2 design decisions, if you don't make at least one of $d'$ or
      $g$ a rational number, this subsitute will return the wrong answer!  Hopefully this design
      will be changed in the future.
      
      Exercise 4.25 (a):
      
      If $C$ is a smooth, nondegenerate space curve and $L$ and $M$ are general lines in
      ${\mathbb P}^3$, how many chords to $C$ meet both $L$ and $M$?  Using our work above,
      we immediately compute:
    Example
      sigma_1 = L_(2,1)
      integral (cycleofchords*(sigma_1)^2)
    Text
      
      Tangent Lines to a Surface
      
      Exercise 4.28:
      
      Using our Grassmannian {\tt G'} with an extra base parameter $d$, we build the cycle
      of tangent lines to a general surface of degree $d$:
    Example
      sigma_1 = K_(2,1)
      tangentcycle = d*(d-1)*sigma_1
    Text
      Now we can compute the number of lines tangent to four general surfaces of degree $d$:
    Example
      tangentlines = integral tangentcycle^4
    Text
      In particular, we calculate the number of lines tangent to four general quadric surfaces:
    Example
      sub(tangentlines, d => 2/1)
///

doc ///
  Key
    "Intersection Theory Section 4.3"
  Headline
    Schubert calculus in general
  Description
    Text
      Subsection 4.3.1
      
      We build arbitrary Schubert cycles using the command {\tt placeholderSchubertCycle}.
      For example, on ${\mathbb G}(2,4)$, we can build the cycle $\sigma_{2,1,1}$ as follows:
    Example
      G24 = flagBundle({3,2})
      sigma_(2,1,1) = placeholderSchubertCycle({2,1,1},G24)
    Text
      
      Subsection 4.3.2
      
      Exercise 4.34
      
      How many lines meet 6 general 2-planes in ${\mathbb P}^4$?
      
      The cycle of lines meeting a 2-plane in the Grassmannian ${\mathbb G}(1,4)$ is the Schubert
      cycle $\sigma_1$, so the number of lines meeting 6 general 2-planes is the degree of
      $(\sigma_1)^6$:
    Example
      G14 = flagBundle({2,3})
      sigma_1 = placeholderSchubertCycle({1,0},G14)
      integral (sigma_1)^6
    Text
      Note that this is the degree of ${\mathbb G}(1,4)$ in the Plucker embedding, since $\sigma_1$
      is the hyperplane class.
      
      Exercise 4.36 (a)
      
      How many lines meet four general $k$-planes in ${\mathbb P}^{2k+1}$?
      
      The cycles of lines meeting a $k$-plane in ${\mathbb G}(1,2k+1)$ is the Schubert cycle
      $\sigma_k$.  We can build a function that calculates this value for any $k$, but we
      cannot use $k$ as a base parameter, since we need to build a different Grassmannian and
      Schubert cycle for each $k$.
    Example
      numOfLines = k -> (
	   G := flagBundle({2,2*k});
	   sigma := placeholderSchubertCycle({k,0}, G);
	   integral sigma^4)
    Text
      Now we can calculate to our hearts' content:
    Example
      for k from 1 to 5 do (
	   << numOfLines(k) << " lines meet four " << k << "-planes in P" << 2*k+1 << "\n")
    Text
      Calculations slow down pretty quickly as $k$ gets large (the bottleneck is building the
      Chow ring), but we suspect the reader will have guessed the correct formula from the 
      above data.
      
      Linear Spaces on Quadrics
      
      Exercise 4.43
      
      A 2-plane in ${\mathbb P}^6$ is the same as a 3-plane in a 7-dimensional space.  According
      to Proposition 4.42, the cycle of 3-planes contained in the zero-locus of a nondegenerate
      quadratic form on a 7-dimensional space is $2^3\sigma_{3,2,1}$ in $G(3,7)$.  Hence we
      calculate:
    Example
      G37 = flagBundle({3,4})
      A37 = intersectionRing G37
      sigma = 8*placeholderSchubertCycle({3,2,1},G37)
      integral sigma^2
    Text
      More generally, we can ask: given 2 general quadrics in ${\mathbb P}^{2k+2}$, how many
      $k$-planes are contained in their intersection?  We calculate:
    Example
      numOfPlanes = k -> (
	   G:= flagBundle({k+1,k+2});
	   schubertlist := apply(k+1,i-> k+1-i); --the list {k+1,k,...,1}
	   sigma := (2^(k+1))*placeholderSchubertCycle(schubertlist, G);
	   integral sigma^2)
      numOfPlanes(2) --This was Exercise 4.43
      for k from 2 to 4 do (
	   << numOfPlanes(k) << " " << k << "-planes in two quadrics in P" << 2*k+2 <<"\n")
    Text
      Exercise 4.44:
      
      Compute $\sigma_{2,1}^2$ in the Chow ring of $G(3,6)$. 
      
      This is easy with the function @TO placeholderToSchubertBasis@, which we already saw in
      @TO "Intersection Theory Section 4.2"@:
    Example
      G36 = flagBundle({3,3})
      c = placeholderSchubertCycle({2,1,0},G36)
      placeholderToSchubertBasis(c^2,G36)
    Text
      We see that $\sigma_{3,2,1}$ occurs with coefficient $2$ in $\sigma_{2,1}^2$.
///

doc ///
  Key
    "Intersection Theory Section 5.2"
  Headline
    Basics of vector bundles and Chern classes
  Description
    Text
      In Schubert2, a vector bundle (or more generally, an @TO AbstractSheaf@) is given by two pieces
      of data: its Chern classes and its rank.  Schubert2 has many built-in bundles for common
      varieties.  For example, a Grassmannian {\tt G} comes with its universal subbundle and
      quotient bundle stored in {\tt G.Bundles}:
    Example
      G = flagBundle({2,3})
      (S,Q) = G.Bundles
      S
      Q
    Text
      The Chern classes of a vector bundle are accessed using the @TO chern@ command:
    Example
      chern(1,Q) -- The first Chern class of Q
      chern Q -- The total Chern class of Q, defined as the sum of the Chern classes of Q.
    Text
      If we want to specify a bundle directly by its Chern classes, we can use the
      @TO abstractSheaf@ command:
    Example
      Q = abstractSheaf(G,ChernClass=>1+H_(2,1)+H_(2,2)+H_(2,3),Rank=>3)
      chern Q
///

doc ///
  Key
    "Intersection Theory Section 5.3"
  Headline
    Operations on vector bundles
  Description
    Text
      Schubert2 has all of the basic operations on vector bundles and their Chern classes built in.
      A full list of all of the available operations can be found in the documentation for
      @TO AbstractSheaf@.  A few examples:
      
      Direct Sums:
    Example
      GG24 = flagBundle({3,2})
      (S,Q) = GG24.Bundles
      B1 = S + Q --direct sum of S+Q
      chern B1
    Text
      Note that the Chern class of $S+Q$ is the same as that of the trivial bundle, since $S$ and $Q$
      fit into an exact sequence whose middle term is trivial (see Prop 5.5).
      
      Tensor Products:
    Example
      B2 = S ** Q --tensor product of S and Q
      chern B2
    Text
      
      Duals:
    Example
      B3 = dual(S) ** Q
      chern B3
    Text
      Note that {\tt B3} is the tangent bundle to $\mathbb{G}(2,4)$.
      
      Pullbacks:
      
      Currently Schubert2 has few morphisms implemented, but given a morphism of abstract varieties,
      it is easy to pull back vector bundles:
    Example
      GG13 = flagBundle({2,2})
      f = GG13 / point -- The structure map of G13
      B = abstractSheaf(point,Rank=>2) -- The trivial vector bundle of rank 2 over point
      f^* B --Pulls back to a trivial bundle of rank 2 on G13
///

doc ///
  Key
    "Intersection Theory Section 5.4.1-2"
  Headline
    Chern class computations on projective space
  Description
    Text
      Subsection 5.4.1 - Universal bundles on projective space
      
      We have two different methods in Schubert2 for producing projective spaces.  We have already
      seen one method: build $\mathbb{P}^n$ as a Grassmannian:
    Example
      P3 = flagBundle({1,3})
      (S,Q) = P3.Bundles
    Text
      In this setting, the the bundle $O(1)$ is the dual of the universal subbundle
      $S$.
    Example
      O1 = dual(S)
      chern O1
    Text
      Now, Schubert2 also comes with a built-in function @TO projectiveSpace@ for making projective
      spaces.  Using {/tt projectiveSpace} to build $\mathbb{P}^n$ is nice, because the resulting
      Chow ring is presented as a truncated polynomial ring in one variable, rather than as a ring
      with $n+1$ generators.  {\bf But, be careful}: this built-in actually produces the projective
      space of 1-{\em quotients}.  For example:
    Example
      P3' = projectiveSpace 3
      (S',Q') = P3'.Bundles
      chern S'
      chern Q' -- Q' is O(1) on P3'
    Text
      
      For the rest of this section, we will use the {\tt flagBundle} method to produce $\mathbb{P}^n$,
      in order to be consistent with the choices in the book.
      
      Subsection 5.4.2
      
      The tangent bundle to projective space comes built-in in Schubert2.  It can be accessed
      via the @TO tangentBundle@ method:
    Example
      T = tangentBundle(P3)
      chern T
    Text
      We can also produce the tangent bundle to $\mathbb{P}^n$ ourselves by using the Euler exact
      sequence:
    Example
      TP3 = (4 * O1) - 1
      chern T == chern TP3
      rank T == rank TP3
    Text
      Note how Schubert2 treats integers in a bundle computation as copies of a trivial bundle.  See
      @TO "AbstractSheaf * AbstractSheaf"@ and @TO "AbstractSheaf - AbstractSheaf"@, for example,
      for more information.
///

doc ///
  Key
    "Intersection Theory Section 5.4.3"
  Headline
    Tangent bundles to hypersurfaces
  Description
    Text      
      Subsection 5.4.3
      
      To treat tangent bundles to hypersurfaces in Schubert2, we have to be a little more careful.
      If $X$ is a hypersurface in ${\mathbb P}^n$, we cannot hope to construct the Chow ring to $X$.
      Even for the case of an elliptic curve $E$ (a degree-3 hypersurface in $\mathbb{P}^2$), the
      construction of $A^1(E)$ amounts to completely understanding the group law on $E$ and all
      points of $E$ (so in particular, this ring is never finitely generated over $\mathbb{C}$),
      and the situation quickly gets worse for higher dimensions and degrees.
      
      However, for classes on $X$ which are obtained by restricting classes on ${\mathbb P}^n$ to $X$,
      we can easily understand a great deal via the projection formula, which in this particular case
      tells us that if $i:X \rightarrow {\mathbb P}^n$ is the inclusion, then
      
      $$i_*(\alpha|_X) = \alpha \cap [X]$$
      
      So, if for example we are interested in calculating the degree of $\alpha|_X$, we can
      equivalently calculate the degree of $\alpha \cap [X]$.  In this way we ``push the problem
      forward'' to ${\mathbb P}^n$.
      
      As an example, if we want to calculate the degree of the top chern class of
      the tangent bundle to a hypersurface $X$ of degree $4$ in ${\mathbb P}^3$, we can compute:
    Example
      P3 = flagBundle({1,3})
      O1 = dual(P3.Bundles#0)
      T = tangentBundle(P3)
      NX = O1^**4 -- the fourth tensor power of O(1), i.e. O(4)
      X = chern(1,NX) -- the fundamental class [X] of X
      TX = chern(T - NX) * X
      integral TX -- The Euler characteristic of a quartic surface
    Text
      This works because we have
      $$c(T_X) = \frac{c(T_P)|_X}{c(N_X)} = \frac{c(T_P)}{c(O_P(X))}|_X.$$
      
      More generally, we can compute the Euler characteristic of a degree-$d$ hypersurface in
      $\mathbb{P}^n$ as in the book.  We can even compute a closed formula for all $d$ and fixed
      $n$ using @TO base@.
    Example
      eulerChar = n -> (
	   S := base d;
	   Pn := flagBundle({1,n},S);
	   TPn := tangentBundle(Pn);
	   O1 := dual(Pn.Bundles#0);
	   NX := O1^**d;
	   TX := chern(TPn - NX)*chern(1,NX);
	   integral TX)
      eulerChar(4) -- The Euler characteristic of a degree-d hypersurface in P4
      sub(eulerChar(4),{d=>4/1}) -- The Euler characteristic of quartic threefold
    Text
      And now we can similarly calculate a formula for the middle Betti number of such a
      hypersurface:
    Example
      middleBetti = n -> (
	   euC := eulerChar(n);
	   ((-1)^(n-1)) * (euC - 2*ceiling((n-1)/2)))
      middleBetti(4) -- The middle Betti number of a degree-d hypersurface in P4
      sub(middleBetti(4), {d => 5/1}) -- The middle Betti number of a quintic threefold
    Text
      Using this, we easily reproduce the table given in the text:
    Example
      for n from 3 to 5 do (
	   for e from 2 to 5 do (
		euC := sub(eulerChar(n),{d=>e/1});
		midB := sub(middleBetti(n),{d=>e/1});
		<< "n: " << n << " d: " << e << " chi: " << euC << " middle Betti: " << midB << endl))
    Text
      
      Exercise 5.11: {\bf Betti numbers of smooth complete intersections}
      
      In the same way as for hypersurfaces, we compute that if $X$ is a complete intersection of
      hypersurfaces of degrees $d_1, \ldots, d_k$ in $P = {\mathbb P}^n$, then
      $$c(T_X) = c(T_P)/(\prod_{i=1}^k c(O_P(d_i)))|_X$$
      We can use then Schubert2 to produce a closed-form formula for the degree of the top Chern class
      of the tangent bundle to a complete intersection of $k$ hypersurfaces in ${\mathbb P}^n$:
    Example
      eulerChar = (n,k) -> (
	   S := base(e_1 .. e_k);
	   Pn := flagBundle({1,n},S);
	   TPn := tangentBundle(Pn);
	   O1 := dual(Pn.Bundles#0);
	   N := sum(1..k, i-> O1^**(e_i)); --the denominator in the above formula
	   X := product(1..k, i->chern(1,O1^**(e_i))); --fundamental class of X
	   TX := chern(TPn - N) * X;
	   integral TX)
      eulerChar(4,2) -- Euler char of a complete intersection surface in P4
    Text
      And from here we can compute the middle Betti numbers:
    Example
      middleBetti = (n,k) -> (
	   euC := eulerChar(n,k);
	   ((-1)^(n-k)) * (euC - 2*ceiling((n-k)/2)))
    Text
      Now our particular problem is easy:
    Example
      sub(middleBetti(4,2),{e_1=>2,e_2=>3/1}) -- complete intersection of a quadric and cubic in P4
      sub(middleBetti(5,3),{e_1=>2,e_2=>2,e_3=>2/1}) -- three quadrics in P5
    Text
      For good measure, we'll also compute the Euler characteristics:
    Example
      sub(eulerChar(4,2),{e_1=>2,e_2=>3/1}) -- complete intersection of a quadric and cubic in P4
      sub(eulerChar(5,3),{e_1=>2,e_2=>2,e_3=>2/1}) -- three quadrics in P5
    Text
      
      Exercise 5.12: {\bf Betti numbers of the quadric line complex}
      
      The only interesting Betti number is the middle one, which we compute immediately from the
      above:
    Example
      sub(middleBetti(5,2),{e_1=>2,e_2=>2/1})
    Text
      
      Exercise 5.13: {\bf Calculate the Euler characteristic of a smooth hypersurface of bidegree}
      $(a,b)$ {\bf in} ${\mathbb P}^m \times {\mathbb P}^n$
      
      Working on ${\mathbb P}^m \times {\mathbb P}^n$ in Schubert2 is easy using relative flag bundles
      (or relative projective spaces): this space is the same as the projectivization of a trivial
      rank-$n+1$ bundle on ${\mathbb P}^m$.  So, for example, to build
      ${\mathbb P}^2 \times {\mathbb P}^3$:
    Example
      P2 = flagBundle({1,2})
      P2xP3 = flagBundle({1,3},P2,VariableNames => K)
      intersectionRing(P2xP3)
    Text
      Note that if we didn't use the {\tt VariableNames} options this ring would be horrible to look
      at, since classes pulled back from ${\mathbb P}^2$ and ${\mathbb P}^3$ would both be named
      $H$.
      
      We can calculate a closed-form formula for the Euler characteristic of a smooth hypersurface
      of bidegree $(a,b)$ once we have fixed $m$ and $n$, but we cannot use $m$ and $n$ as base 
      parameters themselves.
    Example
      eulerChar = (n,m) -> (
	   S := base(a,b);
	   Pn := flagBundle({1,n},S);
	   PnxPm := flagBundle({1,m},Pn);
	   T := tangentBundle(PnxPm);
	   O1Pn := dual(Pn.Bundles#0);
	   f := PnxPm / Pn; -- the first projection map from P2xP3 to P2
	   O10 := f^* O1Pn; -- we pull back O_P2(1) to get O(1,0)
	   O01 := dual(PnxPm.Bundles#0); -- O(0,1)
	   NX := (O10^**a)**(O01^**b); -- O(a,b)
	   X := chern(1,NX); -- Chow class of divisor of type (a,b)
	   TX := chern(T - NX) * X; -- pushed-forward total chern class of tangent bundle to X
	   integral TX) -- chi of a smooth hypersurface of bidegree (a,b) in PnxPm
      eulerChar(4,4) -- chi of a smooth hypersurface of bidegree (a,b) in P4xP4
      sub(eulerChar(2,3),{a=>1,b=>0/1}) -- is P1xP3, should be 8 by Kunneth
      sub(eulerChar(1,1),{a=>1,b=>1/1}) -- a conic in P2, should be 2
      sub(eulerChar(1,1),{a=>2,b=>1/1}) -- a twisted cubic, should be 2 
///

doc ///
  Key
    "Intersection Theory Section 5.4.4"
  Headline
    Bundles on Grassmannians
  Description
    Text
      We already know everything necessary to calculate chern classes of bundles on Grassmannians.
      
      As an example, we can do:
      
      Exercise 5.17: {\bf Calculate the chern classes of the tangent bundle to} ${\mathbb G}(1,3)$
      {\bf in two different ways.}
      
      We calculate directly:
    Example
      G13 = flagBundle({2,2})
      T = tangentBundle(G13)
      chern T
    Text
      The above amounts to using the splitting principle.
      
      We also can calculate the total Chern class of the tangent bundle of $G = {\mathbb G}(1,3)$
      by realizing $G$ as a smooth quadric in ${\mathbb P}^5$.  The plan is the following: first, we'll
      calculate the total Chern class of the tangent bundle in terms of powers of the hyperplane
      section of $G$ in ${\mathbb P}^5$.  Then, we'll substitute $\sigma_1$ into this polynomial,
      since we know $\sigma_1$ is the hyperplane section.
    Example
      P5 = flagBundle({1,5})
      TP5 = tangentBundle(P5)
      O1 = dual(P5.Bundles#0)
      O2 = O1^**2
      TG = chern(TP5 - O2) -- total Chern class of TG in terms of the hyperplane section
                           -- the coefficient of H_(2,i) is the coefficient of sigma_1^i
      sigma_1 = chern(1,G13.Bundles#1)
      1 + sum(1..4, i -> coefficient(chern(i,P5.Bundles#1),TG) * ((sigma_1)^i))
///

doc ///
  Key
    "Intersection Theory Chapter 7"
  Headline
    Lines on Hypersurfaces
  Description
    Text
      Section 7.2.1: Lines on a cubic surface
      
      As in the text, we compute the number of lines on a smooth cubic surface:
    Example
      G13 = flagBundle({2,2})
      (S,Q) = G13.Bundles
      integral chern symmetricPower(3,S)
    Text
      
      Section 7.3: Lines on Quintic Threefolds and Beyond
      
      As in the text, we can calculate the number of lines on a general hypersurface of
      degree $d = 2n-3$ in ${\mathbb P}^n$:
    Example
      netList ({{"n","d", "num of lines"}} |toList apply(3..8, n -> (
		G := flagBundle({2,n-1});
	        (S,Q) := G.Bundles;
	        d = 2*n - 3;
	        {n,d,integral chern symmetricPower(d,dual S)})))
    Text
      
      Exercise 7.19: lines in a quartic threefold
      
      It is easy to construct the class in ${\mathbb G}(1,4)$ of lines in a general quartic
      threefold:
    Example
      G14 = flagBundle({2,3})
      (S,Q) = G14.Bundles
      F1 = ctop symmetricPower(4,dual S) -- ctop = top Chern class
    Text
      Now, we can calculate the degree of the surface $Y$ swept out by these lines in two different
      ways: We can use the fact that the degree of this surface is the number of times it
      meets a generic 2-plane in ${\mathbb P}^4$, which is also the degree of its intersection
      with $\sigma_1$:
    Example
      s = chern(1,Q)
      integral(s*F1)
    Text
      Or we can construct the class of the surface $Y$ directly: consider the usual incidence
      correspondence
      $$I = \{(p,L) | p\in L\} \subset {\mathbb P}^4 \times {\mathbb G}(1,4)$$
      and let $p_1$ and $p_2$ be the projection maps to ${\mathbb P}^4$ and ${\mathbb G}(1,4)$.
      Then we have:
      $$Y = p_1(p_2^{-1}(F))$$
      where $F$ is the Fano variety of lines in our quartic surface.  We can build this
      incidence correspondence in Schubert2 using @TO incidenceCorrespondence@:
    Example
      P4 = flagBundle({1,4})
      I = incidenceCorrespondence(G14,P4)
      I_* F1 -- The surface Y, obtained by pulling back then pushing forward F1 along this correspondence.
    Text
      Here we see that $Y$ is a surface of degree $320$.  These two approaches are related by
      the projection formula; the reader is invited to show their equivalence!
      
      Exercise 7.20:
      
      (a): Find the expected class of the variety of 2-planes on a quadric $Q \subset {\mathbb P}^5$.
      
      As above, we have:
    Example
      G25 = flagBundle({3,3})
      (S,Q) = G25.Bundles
      F2 = ctop symmetricPower(2, dual S)
      placeholderToSchubertBasis(F2,G25)
    Text
      
      (b): Find the expected number of 2-planes on a quartic hypersurface $X \subset {\mathbb P}^7$
    Example
      G27 = flagBundle({3,5})
      (S,Q) = G27.Bundles
      integral ctop symmetricPower(4,dual S)
    Text
      
      Exercise 7.21 - Compute the Fano variety of lines on a complete intersection
      
      Let's use the technique given in the exercise to compute the class of the Fano variety
      of lines in a complete intersection of degrees $(d_1, \ldots, d_k)$ in ${\mathbb P}^n$:
    Example
      linesOnCI := (l,n) -> ( --l is the degree list
	   G := flagBundle({2,n-1});
	   S := G.Bundles#0;
	   product for d in l list (
		ctop(symmetricPower(d,dual S))))
    Text
      So the specific problem of finding the number of lines on a complete intersection of
      two quadrics in ${\mathbb P}^4$ becomes:
    Example
      integral linesOnCI({2,2},4)
///

end
----
restart
loadPackage "IntersectionTheory"
installPackage("IntersectionTheory", RerunExamples=>true)

restart
loadPackage "Schubert2"

X = flagBundle({1,3},VariableNames => K)
Y = flagBundle({2,2},VariableNames => L)
Q = X.Bundles#1
incidenceCorrespondence(X,Y)

IX = flagBundle({1,2},Q, VariableNames => M)
gens intersectionRing IX
gens first flattenRing(intersectionRing IX,CoefficientRing =>QQ)

f = IX/X
(SIX,QIX) = IX.Bundles
IY = flagBundle({1,1},SY, VariableNames => N)
g = IY/Y
QIY = g^* QY 
QQY = IY.Bundles#1 + QIY
(R,k) = flattenRing(intersectionRing IX,CoefficientRing => QQ)
gens R
gensix = (for i from 1 to rank SIX list k(chern(i,SIX)))| (
     for j from 1 to rank QIX list k(chern(j,QIX)))
gensx = (for i from 1 to rank SX list k(chern(i,f^*SX))) | (
     (for j from 1 to rank QX list k(chern(j,f^*QX))))
nicegens = gensix|gensx
targetsix = (for i from 1 to rank SIX list k(chern(i,SIX)))| (
     for j from 1 to rank QIX list k(chern(j,QIX)))
gensx = (for i from 1 to rank S list k(chern(i,f^*S))) | (
     (for j from 1 to rank Q list k(chern(j,f^*Q))))
nicegens = gensix|gensx

targets = (for i from 1 to rank QIY list chern(i,QIY)) | for j from 1 to rank QQY list chern(j,QQY)
subs = for i from 0 to #nicegens-1 list nicegens#i => targets#i

M = sub(vars R, subs) 
R
describe R
prune R


