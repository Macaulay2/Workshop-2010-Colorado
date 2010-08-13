-- -*- coding: utf-8 -*-
--		Copyright 1996-2002,2004 by Daniel R. Grayson

newPackage(
	"SchurRings",
    	Version => "0.2", 
    	Date => "May 23, 2007",
    	Authors => {
	     {Name => "Michael Stillman", Email => "mike@math.cornell.edu", HomePage => "http://www.math.cornell.edu/~mike/"},
	     {Name => "Hal Schenck"}
	     },
    	Headline => "representation rings of general linear groups and of symmetric groups",
    	DebuggingMode => true
    	)

export {schurRing, SchurRing, symmRing, toS, toE, toP, toH, 
     plethysm, jacobiTrudi, Partitions, Schur, Memoize, EorH, CoeffRing,
     zee, symToChar, charToSym, scalarProd, intProd, chi,
     cauchy, wedge,
     PtoE,HtoE,PtoH,EtoH,EtoP,HtoP,HtoETable,EtoHTable,PtoETable,EtoPTable,HtoPTable,PtoHTable,mapToE,mapToP, --take these out
     SchurRingIndexedVariableTable}
-- Improve the names/interface of the following:
--, symmRing, plethysmMap, jacobiTrudi, plethysm, cauchy, bott}

debug Core

SchurRing = new Type of EngineRing
SchurRing.synonym = "Schur ring"
monoid SchurRing := o -> R -> R.monoid
expression SchurRing := S -> new FunctionApplication from { schurRing, (S.Symbol, numgens monoid S) }
undocumented (expression, SchurRing)

toExternalString SchurRing := R -> toString expression R
undocumented (toExternalString, SchurRing),

toString SchurRing := R -> (
     if hasAttribute(R,ReverseDictionary) then toString getAttribute(R,ReverseDictionary)
     else toString expression R)
undocumented (toString, SchurRing)

net SchurRing := R -> (
     if hasAttribute(R,ReverseDictionary) then toString getAttribute(R,ReverseDictionary)
     else net expression R)
undocumented (net, SchurRing)

degreeLength SchurRing := (RM) -> degreeLength monoid RM
coefficientRing SchurRing := Ring => R -> last R.baseRings

ck := i -> if i < 0 then error "expected decreasing row lengths" else i

schur2monom = (a,Mgens) -> (
     if # a === 0 then 1_M
     else product(# a, i -> (Mgens#i) ^ (
	       ck if i+1 < # a 
	       then a#i - a#(i+1)
	       else a#i)))

rawmonom2schur = (m) -> (
     t := new MutableHashTable;
     apply(rawSparseListFormMonomial m, (x,e) -> scan(0 .. x, i -> if t#?i then t#i = t#i + e else t#i = e)); 
     values t
     )

newSchur := (R,M,p) -> (
     if not (M.?Engine and M.Engine) 
     then error "expected ordered monoid handled by the engine";
     if not (R.?Engine and R.Engine) 
     then error "expected coefficient ring handled by the engine";
     RM := R M;
     SR := new SchurRing from rawSchurRing(RM.RawRing);
     SR.Symbol = p;
     SR.baseRings = append(R.baseRings,R);
     commonEngineRingInitializations SR;
     ONE := SR#1;
     if degreeLength M != 0 then (
	  -- there must be something smarter to do, but if we
	  -- do not do this, then we get into an infinite loop
	  -- because each monoid ring ZZ[a,b,c] needs its degrees ring
	  -- ZZ[t], which in turn needs to make its degrees ring 
	  -- ZZ[], which in turn needs one.
	  SR.degreesRing = degreesRing degreeLength M;
	  )
     else (
	  SR.degreesRing = ZZ;
	  );
     if R.?char then SR.char = R.char;
     SR.monoid = M;
     -- SR ? SR := (f,g) -> ( if f == g then symbol == else leadMonomial f ? leadMonomial g ); -- the engine should handle it.
     R * M := (r,m) -> new SR from rawTerm(SR.RawRing,raw r,m.RawMonomial);
     M * R := (m,r) -> new SR from rawTerm(SR.RawRing,raw r,m.RawMonomial);
     SR * M := (p,m) -> p * (R#1 * m);
     M * SR := (m,p) -> (R#1 * m) * p;
     R + M := (r,m) -> r * M#1 + R#1 * m;
     M + R := (m,r) -> r * M#1 + R#1 * m;
     SR + M := (p,m) -> p + R#1 * m;
     M + SR := (m,p) -> p + R#1 * m;
     R - M := (r,m) -> r * M#1 - R#1 * m;
     M - R := (m,r) -> R#1 * m - r * M#1;
     SR - M := (p,m) -> p - R#1 * m;
     M - SR := (m,p) -> R#1 * m - p;
     toExternalString SR := r -> toString expression r;
     expression SR := f -> (
	  (coeffs,monoms) -> sum(
	       coeffs,monoms,
	       (a,m) -> expression (if a == 1 then 1 else new R from a) *
	          new Subscript from {p, (
		    t1 := toSequence rawmonom2schur m;
		    if #t1 === 1 then t1#0 else t1
		    )})
	  ) rawPairs(raw R, raw f);
     listForm SR := (f) -> (
     	  n := numgens SR;
     	  (cc,mm) := rawPairs(raw R, raw f);
     	  toList apply(cc, mm, (c,m) -> (rawmonom2schur m, new R from c)));
     SR.generators = apply(M.generators, m -> SR#(toString m) = SR#0 + m);
     SR.use = x -> (
	  M + M := (m,n) -> R#1 * m + R#1 * n;
	  M - M := (m,n) -> R#1 * m - R#1 * n;
	  - M := (m,n) -> - R#1 * n;
	  scan(SR.baseRings, A -> (
	       if A =!= R then (
		    A * M := (i,m) -> (i * R#1) * m;
		    M * A := (m,i) -> m * (i * R#1);
		    );
	       A + M := (i,m) -> i * R#1 + m;
	       M + A := (m,i) -> m + i * R#1;
	       A - M := (i,m) -> i * R#1 - m;
	       M - A := (m,i) -> m - i * R#1;
	       M / A := (m,r) -> (m * ONE) / (r * ONE);
	       M % A := (m,r) -> (m * ONE) % (r * ONE);
	       ));
	  SR);
     -- leadMonomial R := f -> new M from rawLeadMonomial(n, f.RawRingElement); -- fix this?
     SR
     )

SchurRingIndexedVariableTable = new Type of IndexedVariableTable
SchurRingIndexedVariableTable _ Thing := (x,i) -> x#symbol _ i

schurRing = method (Options => {CoeffRing => ZZ})
schurRing(Thing,ZZ) := SchurRing => opts -> (p,n) -> (
     try p = baseName p else error "schurRing: can't use provided thing as variable";
     if class p === Symbol then schurRing(p,n,opts)
     else error "schurRing: can't use provided thing as variable"
     );
schurRing(Symbol,ZZ) := SchurRing => opts -> (p,n) -> (
--     R := ZZ;
     R := opts.CoeffRing;
     x := local x;
     prune := v -> drop(v, - # select(v,i -> i === 0));
     M := monoid[x_1 .. x_n];
     vec := apply(n, i -> apply(n, j -> if j<=i then 1 else 0));
     -- toString M := net M := x -> first lines toString x;
     S := newSchur(R,M,p);
     dim S := s -> rawSchurDimension raw s;
     Mgens := M.generators;
     t := new SchurRingIndexedVariableTable from p;
     t.SchurRing = S;
     t#symbol _ = a -> ( m := schur2monom(a,Mgens); new S from rawTerm(S.RawRing, raw (1_R), m.RawMonomial));
     S.use = S -> (globalAssign(p,t); S);
     S.use S;
     S)

-- BUG in M2: R_0 .. R_n does not always give elements in the ring R!!
-- workaround:
varlist = (i,j,R) -> apply(i..j, p -> R_p)

symmRings := new MutableHashTable;
symmRing = (n) -> (
     if not symmRings#?n then (
     	  e := global e;
     	  h := global h;
     	  p := global p;
     	  R := QQ[e_1..e_n,p_1..p_n,h_1..h_n,
	       Degrees => toList(1..n,1..n,1..n)];
     	  S := schurRing(symbol s, n);
     	  R.Schur = S;
     	  R.dim = n;
	  
	  degsEHP = toList(1..n);
     	  blocks = {toList(0..(n-1)),toList(n..(2*n-1)),toList(2*n..(3*n-1))};
     	  locVarsE := apply(blocks#0,i->R_i);
     	  locVarsP := apply(blocks#1,i->R_i);
     	  locVarsH := apply(blocks#2,i->R_i);
          R.symRingForE = QQ[locVarsH | locVarsP | locVarsE ,Degrees=>flatten toList(3:degsEHP),MonomialOrder=>GRevLex];
     	  R.mapToE = map(R.symRingForE,R,apply(blocks#2|blocks#1|blocks#0,i->(R.symRingForE)_i));
     	  R.mapFromE = map(R,R.symRingForE,apply(blocks#2|blocks#1|blocks#0,i->R_i));
     	  R.symRingForP = QQ[locVarsH | locVarsE | locVarsP,Degrees=>flatten toList(3:degsEHP),MonomialOrder=>GRevLex];
     	  R.mapToP = map(R.symRingForP,R,apply(blocks#1|blocks#2|blocks#0,i->(R.symRingForP)_i));
     	  R.mapFromP = map(R,R.symRingForP,apply(blocks#2|blocks#0|blocks#1,i->R_i));
     	  PtoE(n,R);
     	  HtoE(n,R);
     	  EtoH(n,R);
     	  PtoH(n,R);
     	  EtoP(n,R);
     	  HtoP(n,R);
     	  R.grbE = forceGB matrix{flatten apply(splice{1..n},i->{R.mapToE(R_(n-1+i))-R.PtoETable#i,R.mapToE(R_(2*n-1+i))-R.HtoETable#i})};
     	  R.grbH = forceGB matrix{flatten apply(splice{1..n},i->{R_(n-1+i)-R.PtoHTable#i,R_(-1+i)-R.EtoHTable#i})};
     	  R.grbP = forceGB matrix{flatten apply(splice{1..n},i->{R.mapToP(R_(-1+i))-R.EtoPTable#i,R.mapToP(R_(2*n-1+i))-R.HtoPTable#i})};
     	  collectGarbage();
     	  R.mapSymToE = (f) -> R.mapFromE(R.mapToE(f)%R.grbE);
     	  R.mapSymToP = (f) -> R.mapFromP(R.mapToP(f)%R.grbP);
     	  R.mapSymToH = (f) -> f%R.grbH;
--	  R.mapSymToE = map(R,R,flatten splice {varlist(0,n-1,R),apply(n, i -> PtoE(i+1,R)),apply(n, i -> HtoE(i+1,R))});
--     	  R.mapSymToP = map(R,R,flatten splice {apply(n, i -> EtoP(i+1,R)), varlist(n,2*n-1,R), apply(n, i -> HtoP(i+1,R))});
--     	  R.mapSymToH = map(R,R,flatten splice {apply(n, i -> EtoH(i+1,R)), apply(n, i -> PtoH(i+1,R)), varlist(2*n,3*n-1,R)});
     	  R.plethysmMaps = new MutableHashTable;
	  symmRings#n = R;
	  );
     symmRings#n)

---------------------------------------------------------------
--------------Jacobi-Trudi-------------------------------------
---------------------------------------------------------------

----local variables for jacobiTrudi
auxR = local auxR;
auxn = local auxn;
auxEH = local auxEH;
----
jacobiTrudi = method(Options => {Memoize => true, EorH => "H"})
jacobiTrudi(Partition,Ring) := opts -> (lambda,R) ->
(
     lam := lambda;
     rez := local rez;
     local u;
     if opts.EorH == "H" then u = h else (u = e;lam = conjugate lam;);
     if opts.Memoize then
     (
	  if not R.?S then R.S = new MutableHashTable;
	  if opts.EorH == "E" then
	  (
     	       -----S#0 records S-functions in terms of e
	       -----S#1 records S-functions in terms of h
	       if not R.S#?0 then R.S#0 = new MutableHashTable;
	       auxEH = 0;
	       )
	  else
	  (
	       if not R.S#?1 then R.S#1 = new MutableHashTable;
	       auxEH = 1;
	       );
     	  auxR = R;
     	  auxn = R.dim;
     	  rez = jT(lam);
	  )
     else
     (
     	  n := #lam;
     	  rez = det map(R^n, n, (i,j) -> 
	       (
	       	    aux := lam#i-i+j;
	       	    if aux < 0 then 0_R
	       	    else if aux == 0 then 1_R else u_aux)
	       )
	  );
     rez
     )
jacobiTrudi(List,Ring) := opts -> (lambda,R) -> jacobiTrudi(new Partition from lambda,R,opts);

jT = (lambda) ->
(
     lambda = toList lambda;
     rez := local rez;
     if auxR.S#auxEH#?lambda then rez = auxR.S#auxEH#lambda
     else
     (
     ll := #lambda;
     if ll == 0 then rez = 1_auxR else
     if ll == 1 then rez = auxR_(2*auxEH*auxn-1+lambda#0) else
     (
	  l1 := drop(lambda,-1);
     	  l2 := {};
	  rez = 0;
	  sgn := 1;
	  for i from 0 to ll-1 do
	  (
     	       rez = rez + sgn*auxR_(2*auxEH*auxn-1+lambda#(ll-1-i)+i)*jT(l1|l2);
	       sgn = - sgn;
	       l1 = drop(l1,-1);
	       if lambda#(ll-1-i)>1 then
	       l2 = {lambda#(ll-1-i)-1} | l2;
	       );
	  );
     auxR.S#auxEH#lambda = rez;
     );
     rez
     )
---------------------------------------------------------------
--------------End Jacobi-Trudi---------------------------------
---------------------------------------------------------------


---------------------------------------------------------------
--------------Plethysm-----------------------------------------
---------------------------------------------------------------
plethysmMap = (d,R) -> (
     -- d is an integer
     -- R is symmRing n
     -- returns the map p_d : R --> R
     --    which sends p_i to p_(i*d).
     n := R.dim;
     if not R.plethysmMaps#?d then (
	 fs := splice {n:0_R,apply(1..(n//d), j -> R_(n-1+d*j)),(2*n-n//d):0_R};
         R.plethysmMaps#d = map(R,R,fs);
	 );
     R.plethysmMaps#d
     )

plethysm = method()
plethysm(RingElement,RingElement) := (f,g) -> (
     -- f is a polynomial in symmRing N
     -- g is a polynomial in symmRing n
     -- result is in symmRing n, in the e basis.
     R := ring g;
     Rf := ring f;
     f = toP f;
     g = toP g;
     n := R.dim;
     N := Rf.dim;
     phi := map(R,Rf,flatten splice {N:0_R,apply(1..N, j -> (plethysmMap(j,R)) g),N:0_R});
     phi f)

plethysm(BasicList,RingElement) := (lambda,g) -> (
     d := sum toList lambda;
     Rf := symmRing d;
     f := jacobiTrudi(lambda,Rf);
     plethysm(f,g))
---------------------------------------------------------------
-----------End plethysm----------------------------------------
---------------------------------------------------------------


---------------------------------------------------------------
----Transition between various types of symmetric functions----
---------------------------------------------------------------
toE = (f) -> (ring f).mapSymToE f
toP = (f) -> (ring f).mapSymToP f
toH = (f) -> (ring f).mapSymToH f

toS = method(Options => {Memoize=>true})
toS(RingElement) := opts -> (f) -> (
     -- f is a polynomial in 'symmRing n', of degree d<=n
     local hf;
     R := ring f;
     rez := 0_(R.Schur);
     n := R.dim;
     d := first degree f;
     use R.Schur;
     if d>n then error"need symmetric ring of higher dimension";
     if opts.Memoize then
     (
     	  hf = toH(f);
     	  while (hf!=0) do
     	  (
     	       lt := leadTerm hf;
     	       (mon,coe) := coefficients lt;
     	       degs := (flatten exponents mon_0_0)_{(2*n)..(3*n-1)};
     	       par := {};
     	       for i from 0 to n-1 do
	           par = par | splice{degs#i:(i+1)};
	       par = reverse par;
	       hf = hf - coe_0_0*(jacobiTrudi(par,R));
	       rez = rez + lift(coe_0_0,coefficientRing R.Schur)*s_par;
     	       );
     )
     else
     (
	  hf = toH(f);
	  ef := toE(f);
	  le := #terms(ef);
	  lh := #terms(hf);
	  if le<lh then 
	  (
	       mtos = map(R.Schur,R,apply(splice{1..n},i->s_(splice{i:1})) | splice{2*n:0});
     	       rez = mtos(ef);
	       )
	  else 	  
	  (
	       mtos = map(R.Schur,R,splice{2*n:0} | apply(splice{1..n},i->s_{i}));
     	       rez = mtos(hf);
	       );
	  );
     rez
     )

PtoE = (m,R) -> (
     -- R is a symmring n
     -- R should have a field named PtoETable, which is
     --  a mutable hash table with i => p_i values for i = 1,...,??
     -- this computes the values up through m.
     n := R.dim;
     if not R.?PtoETable then
     	  R.PtoETable = new MutableHashTable;
     PE := R.PtoETable;
     s := #(keys PE);
--     if (s<m) then
--     (
     for i from s+1 to m do (
	  f := if i > n then 0 else -i*(R.symRingForE)_(2*n+i-1); -- R_(i-1) IS e_i
	  for r from max(1,i-n) to i-1 do 
	       f = f + (-1)^(r-1) * (R.symRingForE)_(2*n+i-r-1) * PE#r; -- R_(i-r-1) IS e_(i-r)
	  PE#i = if i%2 == 0 then f else -f;
	  );
--     initSymR(R);
--     R.grbPE = forceGB matrix{flatten apply(splice{1..m},i->{R.mapToE(R_(n-1+i)-R.PtoETable#i)})};
--     collectGarbage();
--     );
     PE#m
     )

HtoE = (m,R) -> (
     -- R is a symmring n
     -- R should have a field named HtoETable, which is
     --  a mutable hash table with i => e_i values for i = 1,...,??
     -- this computes the values up through m.
     n := R.dim;
     if not R.?HtoETable then
     	  R.HtoETable = new MutableHashTable;
     HE := R.HtoETable;
     s := #(keys HE);
--     if (s<m) then
--     (
     for i from s+1 to m do (
	  f := if i > n then 0 else (-1)^(i-1)*(R.symRingForE)_(2*n+i-1); -- R_(i-1) IS e_i
	  for r from 1 to min(i-1,n-1) do 
	       f = f + (-1)^(r-1) * (R.symRingForE)_(2*n+r-1) * HE#(i-r); -- R_(r-1) IS e_r
	  HE#i = f;
	  );
--     initSymR(R);
--     R.grbHE = forceGB matrix{flatten apply(splice{1..m},i->{R.mapToE(R_(2*n-1+i)-R.HtoETable#i)})};
--     collectGarbage();
--     );
     HE#m
     )

EtoH = (m,R) -> (
     -- R is a symmring n
     -- R should have a field named EtoHTable, which is
     --  a mutable hash table with i => h_i values for i = 1,...,??
     -- this computes the values up through m.
     n := R.dim;
     if not R.?EtoHTable then
     	  R.EtoHTable = new MutableHashTable;
     EH := R.EtoHTable;
     s := #(keys EH);
     if m > n then return 0_R;
--     if (s<m) then
--     (
     for i from s+1 to m do (
	  f := R_(2*n-1+i); -- R_(2*n-1+i) IS h_i
	  for r from 1 to i-1 do 
	       f = f + (-1)^r * EH#r * R_(2*n-1+i-r); -- R_(2*n-1+i-r) IS h_(i-r)
	  EH#i = if i%2 == 1 then f else -f;
	  );
--     initSymR(R);
--     R.grbEH = forceGB matrix{flatten apply(splice{1..m},i->{R_(-1+i)-R.EtoHTable#i})};
--     collectGarbage();
--     );
     EH#m
     )

EtoP = (m,R) -> (
     -- R is a symmring n
     -- R should have a field named EtoPTable, which is
     --  a mutable hash table with i => p_i for i = 1,...,??
     -- this computes the values up through m.
     n := R.dim;
     if not R.?EtoPTable then (
     	  R.EtoPTable = new MutableHashTable;
	  R.EtoPTable#0 = 1;
	  );
     EP := R.EtoPTable;
     s := #(keys EP); -- keys includes 0,1,2,...
     if m > n then return 0_R;
--     if (s<=m) then
--     (
     for i from s to m do (
	  f := 0;
	  for r from 1 to i do 
	       f = f + (-1)^(r-1) * EP#(i-r) * (R.symRingForP)_(2*n-1+r); -- R_(n-1+r) IS p_r
	  EP#i = (1/i) * f;
	  );
--     initSymR(R);
--     R.grbEP = forceGB matrix{flatten apply(splice{1..m},i->{R.mapToP(R_(-1+i)-R.EtoPTable#i)})};
--     collectGarbage();
--     );
     EP#m
     )

HtoP = (m,R) -> (
     -- R is a symmring n
     -- R should have a field named HtoPTable, which is
     --  a mutable hash table with i => h_i for i = 1,...,??
     -- this computes the values up through m.
     n := R.dim;
     if not R.?HtoPTable then (
     	  R.HtoPTable = new MutableHashTable;
	  R.HtoPTable#0 = 1;
	  );
     HP := R.HtoPTable;
     s := #(keys HP); -- keys includes 0,1,2,...
     if m>n then error("need symmetric ring of higher dimension");
--     if (s<=m) then
--     (
     for i from s to m do (
	  f := 0;
	  for r from 1 to i do 
	       f = f + HP#(i-r) * (R.symRingForP)_(2*n-1+r); -- R_(n-1+r) IS p_r
	  HP#i = (1/i) * f;
	  );
--     initSymR(R);
--     R.grbHP = forceGB matrix{flatten apply(splice{1..m},i->{R.mapToP(R_(2*n-1+i)-R.HtoPTable#i)})};
--     collectGarbage();
--     );
     HP#m
     )

PtoH = (m,R) -> (
     -- R is a symmring n
     -- R should have a field named PtoHTable, which is
     --  a mutable hash table with i => p_i for i = 1,...,??
     -- this computes the values up through m.
     n := R.dim;
     if not R.?PtoHTable then (
     	  R.PtoHTable = new MutableHashTable;
	  R.PtoHTable#0 = 1;
	  );
     PH := R.PtoHTable;
     s := #(keys PH); -- keys includes 0,1,2,...
     if m>n then error("need symmetric ring of higher dimension");
--     if (s<=m) then
--     (
     for i from s to m do (
	  f := i*R_(2*n-1+i);  -- R_(2*n-1+i) IS h_i
	  for r from 1 to i-1 do 
	       f = f - PH#r * R_(2*n-1+i-r); -- R_(2*n-1+i-r) IS h_(i-r)
	  PH#i = f;
	  );
--     initSymR(R);
--     R.grbPH = forceGB matrix{flatten apply(splice{1..m},i->{R_(n-1+i)-R.PtoHTable#i})};
--     collectGarbage();
--     );
     PH#m
     )
---------------------------------------------------------------
--------------End transition-----------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
--------------Characters of Symmetric Group--------------------
---------------------------------------------------------------

seqToMults = method()
seqToMults(List) := (lambda) ->
(
     lam := new Partition from lambda;
     aux := toList(conjugate lam)|{0};
     rez := {};
     for j from 0 to #aux-2 do
     (
     	  dif := aux#j-aux#(j+1);
       	  rez = rez | {dif};
	  );
     rez 
     )

multsToSeq = method()
multsToSeq(List) := (mults) ->
(
     n := #mults;
     par := {};
     for i from 0 to n-1 do
         par = par | splice{mults#i:(i+1)};
     reverse par
     )

zee = method()
zee(List) := lambda ->
(
     product for i from 0 to #lambda-1 list((i+1)^(lambda#i)*(lambda#i)!)
     )

symToChar = method()
symToChar(RingElement) := (f)->
(
     R := ring f;
     n := R.dim;
     pf := toP f;
     (mon,coe) := apply(coefficients pf,i->flatten entries i);
--     exps := apply(exponents pf,i->i_{n..(2*n-1)});
     ch := new MutableHashTable;
     for j from 0 to #mon-1 do
     (
     	  degs := (flatten exponents mon#j)_{(n)..(2*n-1)};
     	  par := multsToSeq(degs);
	  ch#par = coe#j * zee(degs);
	  );
     new HashTable from ch
     )

charToSym = method()
charToSym(HashTable,Ring) := (ch,R)->
(
     rez := 0_R;
     n := R.dim;
     for lam in keys ch do
     	  rez = rez + ch#lam * (product for i from 0 to #lam-1 list R_(n-1+lam#i)) / zee(seqToMults lam);
     rez
     )

scalarProd = method()
scalarProd(HashTable,HashTable) := (ch1,ch2)->
(
     scProd := 0;
     chProd := intProd(ch1,ch2);
     for i in keys(chProd) do
     	  scProd = scProd + chProd#i / zee(seqToMults i);
     scProd
     )

scalarProd(RingElement,RingElement) := (f1,f2)->
(
     ch1 = symToChar f1;
     ch2 = symToChar f2;
     scalarProd(ch1,ch2)
     )

intProd = method()
intProd(HashTable,HashTable) := (ch1,ch2)->
(
     iProd := new MutableHashTable;
     l1 := sum((keys ch1)#0);
     l2 := sum((keys ch2)#0);
     if l1 != l2 then error("The symmetric functions/characters must have the same degree");
     for i in keys(ch1) do
     	  if ch2#?i then iProd#i = ch1#i * ch2#i;
     new HashTable from iProd
     )

intProd(RingElement,RingElement) := (f1,f2)->
(
     R := ring f1;
     ch1 = symToChar f1;
     ch2 = symToChar f2;
     charToSym(intProd(ch1,ch2),R)
     )

chi = method()
chi(List,List) := (lambda, rho) ->
(
     ll := sum lambda;
     if ll != sum(rho) then error"Partitions must have the same size.";
     R := symmRing ll;
     sl := jacobiTrudi(lambda,R);
     pr := 1_R;
     for i from 0 to #rho-1 do pr = pr * R_(ll-1+rho#i);
     scalarProd(sl,pr)
     )

---------------------------------------------------------------
--------------End characters-----------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
-----------Partitions related functions------------------------
---------------------------------------------------------------
parts := (d, n) -> (
     -- d is an integer >= 0
     -- n is an integer >= 1
     -- returns a list of all of the partitions of d
     --    having <= n parts.
     x := partitions(d);
     select(x, xi -> #xi <= n))     

-------Generate all the partitions of a set
-------with a given shape
locS = local locS;
locL = local locL;
locLengthL = local locLengthL;
locParts = local locParts;
locPartitions = local locPartitions;
genPartitions = local genPartitions;

genPartitions = method()
genPartitions(ZZ) := (k)->
(
     if k==length locS then (locPartitions = locPartitions | {set toList locParts}) else
     (
     for i from 0 to locLengthL-1 do
     	  if (i==0 and #locParts#0 < locL#0) or (((locL#(i-1)>locL#i) or (#locParts#(i-1)>0)) and (#locParts#i<locL#i)) then
	  (
	       locParts#i = locParts#i + set{locS#k};
	       genPartitions(k+1);
	       locParts#i = locParts#i - set{locS#k};
	       );
     )
);

Partitions = method()
Partitions(Set,List) := (S,L)->
(
     locS = toList S;
     locL = L;
     locLengthL = #L;
     locParts = new MutableList;
     for i from 0 to locLengthL-1 do locParts#i = set{};
     locPartitions = {};
     genPartitions(0);
     locPartitions
     )
Partitions(Set,Partition) := (S,L)-> Partitions(S,toList L)
--------end generate partitions

---------------------------------------------------------------
--------End partitions related functions-----------------------
---------------------------------------------------------------


---------------------------------------------------------------
--------Old stuff----------------------------------------------
---------------------------------------------------------------
cauchy = (i,f,g) -> (
     -- f and g are elements of symmRing's (possibly different)
     -- compute the i th exterior power of the representation f ** g
     P := partitions i;
     n := (ring f).dim;
     n' := (ring g).dim;
     A = schurRing(s,
     result := apply(P, lambda -> (
	       --if #lambda > n or lambda#0 > n' then null
	       --else 
	       (
		   a := toS plethysm(lambda,f);
		   if a == 0 then null
		   else (
			b := toS plethysm(conjugate lambda, g);
			if b == 0 then null else (a,b)
		    ))));
     select(result, x -> x =!= null)
     )

compositions1 = (r,n) -> (
     -- return a list of all of the n-compositions of r.
     -- i.e. ways to write r as a sum of n nonnegative integers
     if n === 1 then {{r}}
     else if r === 0 then {toList(n:0)}
     else (
	  flatten for i from 0 to r list (
	       w := compositions1(r-i,n-1);
	       apply(w, w1 -> prepend(i,w1)))))


pairProduct = L -> (
     -- L is a list of lists of (f,g), f,g both in symm rings.
     -- result: a list of pairs (f,g).
     if #L === 1 then first L
     else (
	  L' := drop(L,1);
	  P' := pairProduct L';
	  flatten apply(L#0, fg -> (
	       (f,g) := fg;
	       apply(P', pq -> (
		    (p,q) := pq;
		    (f*p, g*q)))))
     ))
----e.g. L = {{(h_2,e_3)},{(h_1,e_3),(p_2,e_2)}}
----pairProduct L = {(h_1*h_2,e_3^2), (p_2*h_2,e_2*e_3)}

wedge = method()		    
wedge(List,List) := (C,L) -> (
     -- MES MES: we are working on this function now.  It is fucked up.
     -- the plethysmMap seems messed up.  We really need to make a routine
     -- plethysm(partition,representation)
     -- MES MES
     -- C is a composition of 0..n-1, n == #L
     -- form the product of the exterior powers of the corresponding representations.
     result := {}; -- each entry will be of the form (f,g)
     C0 := positions(C, x -> x =!= 0);
     wedgeL := flatten apply(C0, i -> (
	       apply(L#i, fg -> cauchy(C#i,fg#0,fg#1))));
     pairProduct wedgeL     
     )

wedge(ZZ,List,List) := (r,L,ranks) -> (
     -- r is an integer >= 1
     -- L is a list of pairs (f,g), f,g are in (possibly different) symm rings.
     -- returns wedge(r)(L), as a sum of irreducible representations of GL(m) x GL(n)
     n := #L;
     p := compositions1(r,n);
     p = select(p, x -> all(ranks-x, i -> i>=0));
     join apply(p, x -> wedge(x,L))
     )
--this computes the r-th wedge power of the direct sum of
--V_i\tensor W_i where V_i, W_i are GL(V) and GL(W) modules
--corresponding to pairs of symmetric functions (f_i,g_i)


---------------------------------------------------------------
--------End old stuff----------------------------------------------
---------------------------------------------------------------
end

beginDocumentation()

document {
     Key => "SchurRings",
     Headline => "rings representing irreducible representations of GL(n)",
     "This package make computations in the representation ring of GL(n) possible.",
     PARA{},
     "Given a positive integer ", TT "n", ", 
     we may define a polynomial ring over ", TO "ZZ", " in ", TT "n", " variables, whose
     monomials correspond to the irreducible representations of GL(n), and where 
     multiplication is given by the decomposition of the tensor product of representations",
     PARA{},
     "We create such a ring in Macaulay2 using the ", TO schurRing, " function:",
     EXAMPLE "R = schurRing(s,4);",
     "A monomial represents the irreducible representation with a given highest weight. 
     The standard 4 dimensional representation is",
     EXAMPLE "V = s_{1}",
     "We may see the dimension of the corresponding irreducible representation using ", TO "dim",
     ":",
     EXAMPLE "dim V",
     "The third symmetric power of V is obtained by",
     EXAMPLE {
	  "W = s_{3}",
     	  "dim W"},
     "and the third exterior power of V can be obtained using",
     EXAMPLE {
	  "U = s_{1,1,1}",
	  "dim U"},
     "Multiplication of elements corresponds to tensor product of representations.  The 
     value is computed using a variant of the Littlewood-Richardson rule.",
     EXAMPLE {
	  "V * V",
	  "V^3"},
     "One cannot make quotients of this ring, and Groebner bases and related computations
     do not work, but I'm not sure what they would mean..."
     }

document {
     Key => {schurRing,(schurRing,Symbol,ZZ),(schurRing,Thing,ZZ)},
     Headline => "make a Schur ring",
     TT "schurRing(s,n)", " -- creates a Schur ring of degree n with variables based on the symbol s",
     PARA{"This is the representation ring for the general linear group of ", TT "n", " by ", TT "n", " matrices."},
     PARA{"If ", TT "s", " is already assigned a values as a variable in a ring, its base symbol will be used,
	  if it is possible to determine."},
     SeeAlso => {"SchurRing"}}

document {
     Key => {SchurRing, (degreeLength,SchurRing), (coefficientRing, SchurRing), (monoid, SchurRing)},
     Headline => "the class of all Schur rings",
     "A Schur ring is the representation ring for the general linear group of 
     n by n matrices, and one can be constructed with ", TO schurRing, ".",
     EXAMPLE "R = schurRing(s, 4)",
     "The element corresponding to the Young diagram ", TT "{3,2,1}", " is
     obtained as follows.",
     EXAMPLE "s_{3,2,1}",
     "The dimension of the underlying virtual representation can be obtained
     with ", TO "dim", ".",
     EXAMPLE "dim s_{3,2,1}",
     "Multiplication in the ring comes from tensor product of representations.",
     EXAMPLE "s_{3,2,1} * s_{1,1}",
     SeeAlso => {schurRing}}

-- document {
--      Key => (symbol _, SchurRing, List),
--      Headline => "make an element of a Schur ring",
--      TT "S_v", " -- produce the element of the Schur ring ", TT "S", " corresponding
--      to the Young diagram whose rows have lengths as in the list ", TT "v", ".",
--      PARA{},
--      "The row lengths should be in decreasing order.",
--      SeeAlso => "SchurRing"}

document {
     Key => {SchurRingIndexedVariableTable,(symbol _,SchurRingIndexedVariableTable,Thing)},
     "This class is used as part of the implementation of a type of indexed variable used just for Schur rings.",
     SeeAlso => { IndexedVariableTable }
     }

end
-----------------------------------------------------------------------------
-- the rest of this file used to be schur.m2
-----------------------------------------------------------------------------

-- cauchy = (i,f,g) -> (
--      -- f and g are elements of symmRing's (possibly different)
--      -- compute the i th exterior power of the representation f ** g
--      P := partitions i;
--      n := (ring f).dim;
--      n' := (ring g).dim;
--      result := apply(P, lambda -> (
-- 	       if #lambda > n or lambda#0 > n' then null
-- 	       else (
-- 		    plethysm(lambda, f),
-- 	     	    plethysm(conjugate lambda, g))
-- 		    ));
--      select(result, x -> x =!= null)
--      )

cauchy = (i,f,g) -> (
     -- f and g are elements of symmRing's (possibly different)
     -- compute the i th exterior power of the representation f ** g
     P := partitions i;
     n := (ring f).dim;
     n' := (ring g).dim;
     result := apply(P, lambda -> (
	       --if #lambda > n or lambda#0 > n' then null
	       --else 
	       (
		   a := plethysm(lambda,f);
		   if a == 0 then null
		   else (
			b := plethysm(conjugate lambda, g);
			if b == 0 then null else (a,b)
		    ))));
     select(result, x -> x =!= null)
     )

compositions1 = (r,n) -> (
     -- return a list of all of the n-compositions of r.
     -- i.e. ways to write r as a sum of n nonnegative integers
     if n === 1 then {{r}}
     else if r === 0 then {toList(n:0)}
     else (
	  flatten for i from 0 to r list (
	       w := compositions1(r-i,n-1);
	       apply(w, w1 -> prepend(i,w1)))))


pairProduct = L -> (
     -- L is a list of lists of (f,g), f,g both in symm rings.
     -- result: a list of pairs (f,g).
     if #L === 1 then first L
     else (
	  L' := drop(L,1);
	  P' := pairProduct L';
	  flatten apply(L#0, fg -> (
	       (f,g) := fg;
	       apply(P', pq -> (
		    (p,q) := pq;
		    (f*p, g*q)))))
     ))
----e.g. L = {{(h_2,e_3)},{(h_1,e_3),(p_2,e_2)}}
----pairProduct L = {(h_1*h_2,e_3^2), (p_2*h_2,e_2*e_3)}

wedge = method()		    
wedge(List,List) := (C,L) -> (
     -- MES MES: we are working on this function now.  It is fucked up.
     -- the plethysmMap seems messed up.  We really need to make a routine
     -- plethysm(partition,representation)
     -- MES MES
     -- C is a composition of 0..n-1, n == #L
     -- form the product of the exterior powers of the corresponding representations.
     result := {}; -- each entry will be of the form (f,g)
     C0 := positions(C, x -> x =!= 0);
     wedgeL := flatten apply(C0, i -> (
	       apply(L#i, fg -> cauchy(C#i,fg#0,fg#1))));
     pairProduct wedgeL     
     )

wedge(ZZ,List,List) := (r,L,ranks) -> (
     -- r is an integer >= 1
     -- L is a list of pairs (f,g), f,g are in (possibly different) symm rings.
     -- returns wedge(r)(L), as a sum of irreducible representations of GL(m) x GL(n)
     n := #L;
     p := compositions1(r,n);
     p = select(p, x -> all(ranks-x, i -> i>=0));
     join apply(p, x -> wedge(x,L))
     )

bott = (QRreps) -> (
     -- returns a list of either: null, or (l(w), w.((Qrep,Rrep)+rho) - rho)
     s := QRreps; -- join(Qrep,Rrep);
     rho := reverse toList(0..#s-1);
     s = s + rho;
     len := 0;
     s = new MutableList from s;
     n := #s;
     for i from 0 to n-2 do
     	  for j from 0 to n-i-2 do (
	       if s#j === s#(j+1) then return null;
	       if s#j < s#(j+1) then (
		    tmp := s#(j+1);
		    s#(j+1) = s#j;
		    s#j = tmp;
		    len = len+1;
		    )
	       );
     (len, toList s - rho)
     )

preBott = (i,L,ranks) -> (
     R1 := ring L#0#0#0;
     R2 := ring L#0#0#1;
     dimQ := R1.dim; -- for general bundles we will need to know the ranks concerned
     dimR := R2.dim;
     x := flatten wedge(i,L,ranks);
     x = apply(x, x0 -> (toS x0#0, toS x0#1));
     B := new MutableHashTable;
     scan(x, uv -> (
	       (u,v) := uv;
	       scan(u, u0 -> (
			 scan(v, v0 -> (
			       pQ := u0#0;
			       pR := v0#0;
			       if #pQ < dimQ then
			         pQ = join(pQ,toList((dimQ-#pQ):0));
			       if #pR < dimR then
			         pR = join(pR,toList((dimR-#pR):0));
			       b := join(pQ,pR);
			       c := u0#1 * v0#1;
			       if B#?b then B#b = B#b + c
			       else B#b = c))))));
     B)

doBott = (nwedges,B) -> (
     -- B is the output of preBott
     kB := keys B;
     S := Schur (#(first kB));
     apply(keys B, x -> (
	       b := bott x;
	       if b === null then null
	       else (
		    glb = b#1;
		    d := B#x * dim S_(b#1);
		    (b#0, nwedges - b#0, b#1, B#x, d)))))


weyman = (i,L,ranks) -> (
     B := preBott(i,L,ranks);
     doBott(i,B))

------- old stuff
---- cauchy = (i,L,Rs) -> (
----      -- Rs is a list (R1,R2) of symmRing's, R1 <--> V, R2 <--> W
----      -- L is a list of pairs (f,g), where
----      --   f in R1, g in R2.
----      -- compute the i th exterior power of L.
----      -- 
---- 	       
----      )
---- 
---- jacobiTrudi = (lambda, R) -> (
----      -- lambda is a partition of d
----      -- R is an "hring n", some n.
----      -- returns: s[lambda] as an element of R.
----      n := #lambda;
----      det map(R^n, n, (i,j) -> (
---- 	       p := lambda#i-i+j;
---- 	       if p < 0 then 0_R
---- 	       else if p == 0 then 1_R else h_p))
----      )
---- htos = (d,R) -> (
----      -- d is an integer >= 0
----      -- R is an 'hring n'
----      if not R.?toSchur then R.toSchur = new MutableHashTable;
----      if not R.toSchur#?d then (
----      	  n := numgens R;
----      	  P := parts(d,n);
----      	  S := matrix {apply(P, x -> jacobiTrudi(x,R)) };
----      	  H := transpose basis(d,R);
----      	  B := transpose contract(H,S);
---- 	  R.toSchur#d = (H,B^(-1), P);
---- 	  );
----      R.toSchur#d
----      )     
---- 
---- tos = (f) -> (
----      -- f is a homogeneous polynomial in 'hring n', of degree d
----      d := first degree f;
----      R := ring f;
----      (H,C,P) := htos(d,R);
----      fInS := transpose contract(H,matrix{{f}}) * C;
----      fInS = flatten entries fInS;
----      fInS = apply(fInS, x -> if x == 0 then 0 else leadCoefficient(x));
----      S := R.Schur;
----      sum apply(#P, i -> fInS_i * S_(P_i))
----      )
     
end

-----------------------------------------------------------------------------
-- some tests that can be incorporated into the documentation later
-----------------------------------------------------------------------------

restart
loadPackage "SchurRings"
debug SchurRings
R = symmRing 4
toE s_{2}
describe R
toS(e_1*e_2*e_3)
toSf = map(ring oo, R, apply(gens R, x -> toS x))
toSf(e_1*e_2*e_3)

f = jacobiTrudi({2},R)
plethysm(f,e_1)
f = jacobiTrudi({2,1},R)
f = jacobiTrudi({2,2},R)
f = jacobiTrudi({3,2,1},R)

toSf f
toS f
f = jacobiTrudi({2,1},R)
toE toP f

toP jacobiTrudi({2},R)
toP jacobiTrudi({1,1,1,1},R)
toP jacobiTrudi({4,4,4,4},R)
toP e_4

R = symmRing 5
PtoE(1,R)
PtoE(2,R)
PtoE(3,R)
PtoE(4,R)
PtoE(5,R)

EtoP(1,R)
EtoP(2,R)
EtoP(3,R)
EtoP(4,R)
EtoP(5,R)

apply(1..10, i -> toP(PtoE(i,R)))
apply(1..5, i -> toE(EtoP(i,R)))

toE EtoP(1,R)
toE EtoP(2,R)
toE EtoP(3,R)
toE EtoP(4,R)

toP PtoE(1,R)
toP PtoE(2,R)
toP PtoE(3,R)
toS toE toP PtoE(4,R)
toS PtoE(4,R)
PtoE(4,R)

toS (jacobiTrudi({2,1},R))^2
R.Schur_{2,1}^2

f = toS plethysm(jacobiTrudi({2},R), jacobiTrudi({2},R)) -- assert(f == {({4}, 1), ({2, 2}, 1)})
f = toS plethysm(jacobiTrudi({3},R), jacobiTrudi({2},R)) -- assert(f == 
f = toS plethysm(jacobiTrudi({2,1},R), jacobiTrudi({2},R)) -- assert(f == 
f = toS plethysm(jacobiTrudi({1,1,1},R), jacobiTrudi({2},R)) -- assert(f == 
toS (jacobiTrudi({1},R))^3
ps2 = plethysm(e_2, e_1^2 - e_2)
toP ps2
toS ps2
toP e_2
toP (e_1^2-e_2)

PtoE(20,R)
R = symmRing 6
PtoE(4,R)
PtoE(12,R)

R = symmRing 4
apply(1..20, i -> PtoE(i,R) - PtoE(i,R))
PtoE(30,R)
R = symmRing 6
PtoE(12,R)
apply(1..10, i -> PtoE(i,R) - PtoE(i,R))
time PtoE(12,R)

plethysmMap(3,R)

R10 = symmRing 10
R = symmRing 3
f = toS plethysm(jacobiTrudi({10},R10), jacobiTrudi({2},R)) -- assert(f == {({4}, 1), ({2, 2}, 1)})

R = symmRing 5
f = toS plethysm(jacobiTrudi({1,1},R), jacobiTrudi({2},R)) -- {3,1}
f = toS plethysm(jacobiTrudi({1,1},R), jacobiTrudi({3},R)) -- {5,1} + {3,3}


--------------------
-- test of cauchy --
--------------------
restart
load "schur.m2"
R1 = symmRing 5
f = jacobiTrudi({2},R1)
g = jacobiTrudi({1},R1)
cauchy(2,f,g)
cauchy(3,f,g)
R1 = symmRing 1
R2 = symmRing 2
cauchy(2,jacobiTrudi({1},R1),jacobiTrudi({2},R2))
toS oo_0_1
cauchy(3,1_R1,jacobiTrudi({3},R2))
toS oo_0_1
--------------------
-- test of bott ----
--------------------
restart
load "schur.m2"
R1 = symmRing 5
bott({0,3,0}) == (1, {2, 1, 0})
bott({1,2,0}) === null
bott({2,1,0}) == (0, {2, 1, 0})
bott({2,4,0}) == (1, {3, 3, 0})
bott({0,3,3}) == (2, {2, 2, 2})
bott({3,2,1,20,10,1})
--------------------
-- test of pairProduct
--------------------
restart
load "schur.m2"
R1 = symmRing 1
R2 = symmRing 2
L = {{(1_R1, jacobiTrudi({3},R2))}, 
     {(jacobiTrudi({1},R1), jacobiTrudi({2},R2))}, 
     {(jacobiTrudi({2},R1), jacobiTrudi({1},R2))}}
pairProduct L
L1 = drop(L,1)
pairProduct L1
wedge({2,1,0},L)
c1 = cauchy(3,L#0#0#0, L#0#0#1)
c2 = cauchy(2,L#1#0#0, L#1#0#1)
(c1_0)/toS
(c2_0)/toS
(c2_1)/toS
wedge({3,2,0},L)
L#0#0#0
L#0#0#1

L/(v -> (toS v#0#1))

--------------------
-- test of plethysm
--------------------
restart
load "schur.m2"
R = symmRing 2
plethysm({1,1},jacobiTrudi({2},R))
toS oo
plethysm({1,1,1},jacobiTrudi({4},R))
toS oo
--------------------
-- test of wedge
--------------------
restart
load "schur.m2"
R1 = symmRing 1
R2 = symmRing 2
L = {{(1_R1, jacobiTrudi({3},R2))}, 
     {(jacobiTrudi({1},R1), jacobiTrudi({2},R2))}, 
     {(jacobiTrudi({2},R1), jacobiTrudi({1},R2))}}
wedge({3,2,0},L)
wedge({3,0,0},L)
z = preBott(1,L,{4,3,2})
doBott(5,z)

weyman(1,L,{4,3,2})
weyman(2,L,{4,3,2})
weyman(3,L,{4,3,2})
weyman(4,L,{4,3,2})
weyman(5,L,{4,3,2})
weyman(6,L,{4,3,2})
weyman(7,L,{4,3,2})
weyman(8,L,{4,3,2})
weyman(9,L,{4,3,2})
--------------------
restart
load "schur.m2"
R1 = symmRing 1
R2 = symmRing 3
L = {{(1_R1, jacobiTrudi({4},R2))}, 
     {(jacobiTrudi({1},R1), jacobiTrudi({3},R2))}, 
     {(jacobiTrudi({2},R1), jacobiTrudi({2},R2))},
     {(jacobiTrudi({3},R1), jacobiTrudi({1},R2))}}
wedge({3,2,0},L)
wedge({3,0,0},L)
z = preBott(1,L,{4,3,2})
doBott(5,z)

weyman(1,L,{15,10,6,3})
weyman(2,L,{15,10,6,3})
weyman(3,L,{15,10,6,3})
weyman(4,L,{15,10,6,3})
weyman(7,L,{15,10,6,3})
weyman(15,L,{15,10,6,3})

y

weyman(2,L,{4,3,2})
weyman(3,L,{4,3,2})
weyman(4,L,{4,3,2})
weyman(5,L,{4,3,2})
weyman(6,L,{4,3,2})
weyman(7,L,{4,3,2})
weyman(8,L,{4,3,2})
weyman(9,L,{4,3,2})
	       
--------------------
#(compositions1(9,3))



n = 3
--R = QQ[x_1 .. x_n]
p = symbol p
R = QQ[x_1 .. x_n, p_1 .. p_n, MonomialOrder => ProductOrder {n,n}]
slambda = (lambda) -> (
     map(R^n, n, (i,j) -> x_(i+1)^(lambda#j+n-j-1))
     )

schur = (lambda) -> (
     p := toList(#lambda:0);
     det slambda(lambda) // det slambda p)


end

restart
load "schur.m2"
(H,E,P,S) = symmRings 4
f = jacobiTrudi({4,1},E)
tos f 
tos f == S_{4,1}
f = jacobiTrudi({2,1},E)
tos f
tos f == S_{2,1}
f = jacobiTrudi({7,4,2},E)
tos f
tos f == S_{2,1}


R = hring 4
describe R
f = jacobiTrudi([2,1],R)
tos f




f = jacobiTrudi([4,1],H)
tos f

dualPartition {4,1}

dualPartition {4,2,2,1,1}
dualPartition {5,4,4,4,1}
dualPartition {2,2,2,2}

htos(3,R)

parts(3,1)
parts(3,2)
parts(3,3)
parts(0,1)
parts(1,1)

schur {2,1,0}
schur {2,0,0}
schur {1,1,1}

I = ideal apply(n, i -> p_(i+1) - sum apply(n, j -> x_(j+1)^(i+1)))
schur{2,0,0}  % I
schur{2,1,0} % I
schur{1,1,1} % I
exponents oo

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=SchurRings pre-install"
-- End:

------Claudiu
restart
loadPackage "SchurRings"
time R = symmRing 30


----wedge powers over GL(V) x GL(W)
A = symmRing 12
B = symmRing 15
cauchy(3,A_3,B_32)
wedge(3,{{(A_2,B_3)},{(A_1,B_2)}},{4,4})

use B
wedge(3,{{(h_2,e_3)},{(e_1,e_2)},{(h_2,h_2)}},{4,4,4})
----end wedge powers

----Scalar products
s_{3,3,3}*s_{4,2,1}
scalarProd(jacobiTrudi({6,4,3,2,1},R),jacobiTrudi({3,3,3},R)*jacobiTrudi({4,2,1},R))
scalarProd(jacobiTrudi({6,4,3,2,1},R),jacobiTrudi({4,3,3,3,2,1},R))

s_{6,4,4,2}*s_{3,3,3,2,1,1,1}
time scalarProd(jacobiTrudi({6,4,4,2},R)*jacobiTrudi({3,3,3,2,1,1,1},R),jacobiTrudi({6,6,5,3,3,2,2,1,1,1},R))
-----end scalar products

-----characters
time for lam in partitions(5) do
     print (lam,symToChar(jacobiTrudi(lam,R)))
chi({2,1,1,1},{2,1,1,1})
chi({3,1,1},{1,1,1,1,1})
chi({3,2},{3,1,1})
chi({2,2,1},{3,1,1})
chi({3,1,1},{2,2,1})
-------end characters


-----transition to s-functions, J-Trudi
use R
time toS(h_1^20,Memoize=>true);
time toS(h_1^20,Memoize=>false);

time toS(plethysm(h_5,h_4),Memoize=>true);
time toS(plethysm(h_5,h_4),Memoize=>false);

time jacobiTrudi({7,7,5,4,3,2,2},R,Memoize=>true);
time jacobiTrudi({7,7,5,4,3,2,2},R,Memoize=>false);

time toS(plethysm(h_5,h_6),Memoize=>true);
time toS(plethysm(h_5,h_6),Memoize=>false);

time toS(e_30,Memoize=>true)
time toS(e_30,Memoize=>false)

time toS(h_30,Memoize=>true)
time toS(h_30,Memoize=>false)

time jacobiTrudi(splice{30:1},R);
-----end transition to s-functions, J-Trudi

restart
loadPackage "SchurRings"
time R = symmRing 10
S = schurRing(y,10,CoeffRing => R)
h_3*y_{4}^2+h_2*y_{2,1}*y_{3}
