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

export {grassmannian, placeholderSchubertCycle, diagrams, placeholderToSchubertBasis}

needsPackage "Schubert2"

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
	  bi = b#i;
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
	  --should maybe add option to choose variable name
	  S = B[apply(P, i-> s_i)]; --poly ring with generators <=> schubert basis elts
	  R.cache.schubertring = S;
	  S.cache = new MutableHashTable;
	  S.cache.intersectionmap = map(R,S,M));
     (vars S)*(lift(c2,B))
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
      ***Set range to: from 1 to 8 in final draft***
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
      sigma = 8*placeholderSchubertCycle({3,2,1},G37)
      integral sigma^2
    Text
      More generally, we can ask: given 2 general quadrics in ${\mathbb P}^{2k+2}$, how many
      $k$-planes are contained in their intersection?  We calculate:
      ***set range to: from 2 to 5 in final draft***
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
      Exercise 4.44
      
      This is easy with the function @TO placeholderToSchubertBasis@, which we already saw in
      @TO "Intersection Theory Section 4.2"@:
    Example
      G36 = flagBundle({3,3})
      c = placeholderSchubertCycle({2,1,0},G36)
      placeholderToSchubertBasis(c^2,G36)
    Text
      We see that $\sigma_{3,2,1}$ occurs with coefficient $2$ in $\sigma_{2,1}^2$.
///

