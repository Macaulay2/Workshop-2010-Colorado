-- -*- coding: utf-8 -*-
--		Copyright 1996-2002,2004 by Daniel R. Grayson

newPackage(
	"SchurRings",
    	Version => "0.5", 
    	Date => "February 12, 2011",
    	Authors => {
	     {Name => "Michael Stillman", Email => "mike@math.cornell.edu", HomePage => "http://www.math.cornell.edu/~mike/"},
	     {Name => "Hal Schenck"},
	     {Name => "Claudiu Raicu"}
	     },
    	Headline => "representation rings of general linear groups and of symmetric groups",
    	DebuggingMode => true,
	AuxiliaryFiles => true
    	)

--schurRing(coefficientRing)
--schurRing(coefficientRing,ZZ)
--symmRing(coefficientRing,ZZ)
--symmRing(coefficientRing) -- options -> names of e,h,p variables
--     	    	      	    -- maybe coefficientRing is an option

--plethysm should work for tensor products of schurRings, or symmRings

--longer names for
--toE => 
--toH =>
--toP =>
--toS =>


export {schurRing, SchurRing, symmRing,
     symmetricRingOf, schurRingOf,
     toS, toE, toP, toH,
     jacobiTrudi, plethysm,
     centralizerSize, classFunction, symmetricFunction, 
     scalarProduct, internalProduct,
     SchurRingIndexedVariableTable, EHPSVariables,
     ClassFunction, schurLevel,
     
     Memoize, Schur, EorH,
     eVariable, pVariable, hVariable, getSchur
--     cauchy, wedge, preBott, bott, doBott, weyman
     }

debug Core

protect symbol symRingForE;
protect symbol mapToE;
protect symbol symRingForP;
protect symbol mapToP;
protect symbol mapFromP;
protect symbol grbE
protect symbol PtoETable
protect symbol HtoETable
protect symbol grbH
protect symbol PtoHTable
protect symbol EtoHTable
protect symbol grbP
protect symbol EtoPTable
protect symbol HtoPTable
--protect symbol plethysmMaps
protect symbol mapFromE
protect symbol sFunction


SchurRing = new Type of EngineRing
SchurRing.synonym = "Schur2 ring"

expression SchurRing := S -> new FunctionApplication from { schurRing, (expression last S.baseRings, S.Symbol, S.numgens ) }
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

rawmonom2partition = (m) -> (
     reverse splice apply(rawSparseListFormMonomial m, (x,e) -> e:x)
     )

SchurRing _ List := (SR, L) -> new SR from rawSchurFromPartition(raw SR, L)
--SchurRing _ List := (SR, L) -> new SR from rawSchurFromPartition(raw SR,select(L,i->i>0))
SchurRing _ Sequence := (SR, L) -> new SR from rawSchurFromPartition(raw SR, L)
SchurRing _ ZZ := (SR, L) -> new SR from rawSchurFromPartition(raw SR, 1:L)
coefficientRing SchurRing := Ring => R -> last R.baseRings
numgens SchurRing := Ring => R -> R.numgens

symmetricRingOf = method()
symmetricRingOf (Ring) := R -> (
     	  if R.?symmRing then R.symmRing else
	  if class R === SchurRing then
	  (
	       if numgens R === infinity then 
	          error"symmetric ring expects finite schurRings";
     	       if coefficientRing R === ZZ then
	       	  error"base ring has to be QQ";
     	       R.symmRing = symmRing(symmetricRingOf coefficientRing R,numgens R);
     	       R.symmRing.Schur = R;
	       R.symmRing
	       )
	  else R
     )

schurRingOf = method()
schurRingOf (Ring) := R -> (
     	  if R.?Schur then R.Schur else
	  if schurLevel R > 0 then
	  (
	       if instance(R, SchurRing) then R else
	       (
		    s := getSymbol "s";
     	       	    R.Schur = schurRing(symmetricRingOf coefficientRing R,s,R.dim);
     	       	    R.Schur.symmRing = R;
	       	    R.Schur
		    )
	       )
	  else error"Expected ring to have a Schur Ring"
     )

schurLevel = method()
schurLevel (Ring) := R -> if R.?schurLevel then R.schurLevel else 0

newSchur2 = method()
newSchur2(Ring,Symbol) := (A,p) -> newSchur2(A,p,-1)
       
newSchur2(Ring,Symbol,ZZ) := (A,p,n) -> (
     if not (A.?Engine and A.Engine) 
     then error "expected coefficient ring handled by the engine";
     SR := new SchurRing from rawSchurRing1(raw A,n);
     SR.Symbol = p;
     SR.baseRings = append(A.baseRings,A);
     SR.generators = {};
     SR.numgens = if n < 0 then infinity else n;
     SR.degreeLength = 0;
     commonEngineRingInitializations SR;
     ONE := SR#1;
     if A.?char then SR.char = A.char;
     toExternalString SR := r -> toString expression r;
     expression SR := f -> (
	  (coeffs,monoms) -> sum(
	       coeffs,monoms,
	       (a,m) -> expression (if a == 1 then 1 else new A from a) *
	          new Subscript from {p, (
		    t1 := toSequence rawmonom2partition m;
		    if #t1 === 1 then t1#0 else t1
		    )})
	  ) rawPairs(raw A, raw f);
     listForm SR := (f) -> (
     	  n := numgens SR;
     	  (cc,mm) := rawPairs(raw A, raw f);
     	  toList apply(cc, mm, (c,m) -> (rawmonom2partition m, new A from c)));
     if (A.?schurLevel) then SR.schurLevel = A.schurLevel + 1
     else SR.schurLevel = 1;
     SR
     )

schurRing = method(Options => {EHPSVariables => (getSymbol"e",getSymbol"h",getSymbol"p",getSymbol"s")})
schurRing(Ring,Thing,ZZ) := SchurRing => opts -> (A,p,n) -> (
     try p = baseName p else error "schurRing: can't use provided thing as variable";
     if class p === Symbol then schurRing(A,p,n,opts)
     else error "schurRing: can't use provided thing as variable"
     );
schurRing(Ring,Thing) := SchurRing => opts -> (A,p) -> (
     try p = baseName p else error "schurRing: can't use provided thing as variable";
     if class p === Symbol then schurRing(A,p,opts)
     else error "schurRing: can't use provided thing as variable"
     );

schurRing(Ring,Symbol) := opts -> (R,p) -> schurRing(R,p,infinity,opts)
schurRing(Ring,Symbol,InfiniteNumber) := 
schurRing(Ring,Symbol,ZZ) := SchurRing => opts -> (R,p,n) -> (
     S := newSchur2(R,p,n);
     dim S := s -> dimSchur(s);
     dim(Thing,S) := (n,s) -> dimSchur(n, s);
     t := new SchurRingIndexedVariableTable from p;
     t.SchurRing = S;
     t#symbol _ = a -> ( S _ a);
     S.use = S -> (globalAssign(p,t); S);
     S.use S;
     S)
schurRing(Thing,ZZ) := (s,n) -> schurRing(ZZ,s,n)

SchurRingIndexedVariableTable = new Type of IndexedVariableTable
SchurRingIndexedVariableTable _ Thing := (x,i) -> x#symbol _ i

symmRing = method(Options => options schurRing)
symmRing (Ring,ZZ) := opts -> (A,n) -> (
     	  (e,h,p,s) := opts.EHPSVariables;
     	  R := A[e_1..e_n,p_1..p_n,h_1..h_n,
	    Degrees => toList(1..n,1..n,1..n), MonomialSize => 8];
     	  R.EHPSVariables = opts.EHPSVariables;
       	  R.eVariable = (i) -> R_(i-1);
	  R.pVariable = (i) -> R_(n+i-1);
	  R.hVariable = (i) -> R_(2*n+i-1);
     	  R.dim = n;
	  
	  degsEHP := toList(1..n);
     	  blocks := {toList(0..(n-1)),toList(n..(2*n-1)),toList(2*n..(3*n-1))};
     	  vrs := symbol vrs;
     	  locVarsE := apply(blocks#0,i->vrs_i);
     	  locVarsP := apply(blocks#1,i->vrs_i);
     	  locVarsH := apply(blocks#2,i->vrs_i);
          R.symRingForE = A[locVarsH | locVarsP | locVarsE ,Degrees=>flatten toList(3:degsEHP),MonomialOrder=>GRevLex, MonomialSize => 8];
     	  R.mapToE = map(R.symRingForE,R,apply(blocks#2|blocks#1|blocks#0,i->(R.symRingForE)_i));
     	  R.mapFromE = map(R,R.symRingForE,apply(blocks#2|blocks#1|blocks#0,i->R_i));
     	  R.symRingForP = A[locVarsH | locVarsE | locVarsP,Degrees=>flatten toList(3:degsEHP),MonomialOrder=>GRevLex, MonomialSize => 8];
     	  R.mapToP = map(R.symRingForP,R,apply(blocks#1|blocks#2|blocks#0,i->(R.symRingForP)_i));
     	  R.mapFromP = map(R,R.symRingForP,apply(blocks#2|blocks#0|blocks#1,i->R_i));
     	  EtoP(n,R);
     	  PtoE(n,R);
     	  HtoE(n,R);
     	  EtoH(n,R);
     	  PtoH(n,R);
     	  HtoP(n,R);
     	  R.grbE = forceGB matrix{flatten apply(splice{1..n},i->{R.mapToE(R_(n-1+i))-R.PtoETable#i,R.mapToE(R_(2*n-1+i))-R.HtoETable#i})};
     	  R.grbH = forceGB matrix{flatten apply(splice{1..n},i->{R_(n-1+i)-R.PtoHTable#i,R_(-1+i)-R.EtoHTable#i})};
     	  R.grbP = forceGB matrix{flatten apply(splice{1..n},i->{R.mapToP(R_(-1+i))-R.EtoPTable#i,R.mapToP(R_(2*n-1+i))-R.HtoPTable#i})};
     	  collectGarbage();
     	  R.mapSymToE = (f) -> R.mapFromE(R.mapToE(f)%R.grbE);
     	  R.mapSymToP = (f) -> R.mapFromP(R.mapToP(f)%R.grbP);
     	  R.mapSymToH = (f) -> f%R.grbH;
--     	  R.plethysmMaps = new MutableHashTable;
	  if (A.?schurLevel) then R.schurLevel = A.schurLevel + 1
     	  else R.schurLevel = 1;
     	  R)
---------------------------------------------------------------
--------------Jacobi-Trudi-------------------------------------
---------------------------------------------------------------

----local variables for jacobiTrudi
auxR = local auxR;
auxn = local auxn;
auxEH = local auxEH;
----

jacobiTrudi = method(Options => {Memoize => true, EorH => "E"})
jacobiTrudi(BasicList,Ring) := opts -> (lambda,R) ->
(
     lam := new Partition from lambda;
     rez := local rez;
     local u;
     if opts.EorH == "H" then u = R.hVariable else (u = R.eVariable;lam = conjugate lam;);
     if opts.Memoize then
     (
	  if not R.?sFunction then R.sFunction = new MutableHashTable;
	  if opts.EorH == "E" then
	  (
     	       -----S#0 records S-functions in terms of e
	       if not R.sFunction#?0 then R.sFunction#0 = new MutableHashTable;
	       auxEH = 0;
	       )
	  else
	  (
	       -----S#1 records S-functions in terms of h
	       if not R.sFunction#?1 then R.sFunction#1 = new MutableHashTable;
	       auxEH = 1;
	       );
     	  auxR = R;
     	  auxn = R.dim;
     	  rez = jT(lam);
	  )
     else
     (
     	  n := #lam;
     	  rez = det(map(R^n, n, (i,j) -> 
	       (
	       	    aux := lam#i-i+j;
	       	    if aux < 0 or aux>R.dim then 0_R
	       	    else if aux == 0 then 1_R else u aux)
	       ),
	  Strategy => Cofactor);
	  );
     rez
     )

jT = (lambda) ->
(
     lambda = toList lambda;
     rez := local rez;
     if auxR.sFunction#auxEH#?lambda then rez = auxR.sFunction#auxEH#lambda
     else
     (
     ll := #lambda;
     if ll == 0 or lambda#0 == 0 then rez = 1_auxR else
     if ll == 1 then rez = auxR_(2*auxEH*auxn-1+lambda#0) else
     (
	  l1 := drop(lambda,-1);
     	  l2 := {};
	  rez = 0;
	  sgn := 1;
	  for i from 0 to ll-1 do
	  (
     	       if lambda#(ll-1-i)+i<=auxn then --just added, won't work for h-polynomials
	       rez = rez + sgn*auxR_(2*auxEH*auxn-1+lambda#(ll-1-i)+i)*jT(l1|l2);
	       sgn = - sgn;
	       l1 = drop(l1,-1);
	       if lambda#(ll-1-i)>1 then
	       l2 = {lambda#(ll-1-i)-1} | l2;
	       );
	  );
     auxR.sFunction#auxEH#lambda = rez;
     );
     rez
     )
---------------------------------------------------------------
--------------End Jacobi-Trudi---------------------------------
---------------------------------------------------------------


---------------------------------------------------------------
--------------Plethysm-----------------------------------------
---------------------------------------------------------------
plethysmMap = (d,maxg,R) -> (
     -- d is an integer
     -- R is symmRing n
     -- returns the map p_d : R --> R
     --    which sends p_i to p_(i*d).
     auxS := R;
     lev := schurLevel R;
     fs := {};
     local nS;
     local nSd;
     while lev > 0 do
     (
     	  nS = auxS.dim;
          nSd = nS//d; 
     	  fs = join(fs,splice{nS:0_auxS});
	  topf := min(maxg#(lev-1),nSd);
	  fs = join(fs, apply(1..topf, j -> auxS_(nS-1+d*j)));
	  if maxg#(lev-1)>nSd then fs = join(fs, apply(topf+1..maxg#(lev-1),j-> auxS.mapFromE auxS.PtoETable#(d*j)));
	  fs = join(fs, 2*nS-maxg#(lev-1):0_auxS);
	  auxS = coefficientRing auxS;
	  lev = schurLevel auxS;
	  );
	 map(R,R,fs)
--         R.plethysmMaps#d = map(R,R,fs);
--	 );
--     R.plethysmMaps#d
     )

plethysm = method()
plethysm(RingElement,RingElement) := (f,g) -> (
     -- f is a polynomial in symmRing N / SchurRing SA
     -- g is a polynomial in symmRing n / SchurRing SB
     -- result is in symmRing n / SchurRing SB
     Rg := ring g;
     Rf := ring f;
     if schurLevel Rf > 1 then error"Undefined plethysm operation";

     issy := not instance(Rg,SchurRing);
     pg := toP g;
     pf := toP f;
     
     SRg := ring pg;
     SRf := ring pf;
          
     nf := SRf.dim;
     maxf := max(support(pf)/index//max-nf+1,0);
     
     auxS := SRg;
     nS := auxS.dim;
     lev := schurLevel auxS;
     maxg := {};
     spg := support(pg)/index;
     local ma;
     while lev>0 do
     (
     	  ma = max(select(spg,i->i<3*nS)//max-nS+1,0);
	  if maxf*ma >= #auxS.PtoETable then PtoE(maxf*ma,auxS);
	  maxg = join({ma},maxg);
	  spg = select(spg,i->i>=3*nS)/(j->j-3*nS);
     	  auxS = coefficientRing auxS;
	  nS = auxS.dim;
	  lev = schurLevel auxS;
	  );
     phi := map(SRg,SRf,flatten splice {nf:0_SRg,
	       apply(1..nf, j -> (if j<=maxf then (plethysmMap(j,maxg,SRg))pg else 0_SRg)),
	       nf:0_SRg});
     pl := phi pf;
     if issy then pl else toS pl
)

plethysm(BasicList,RingElement) := (lambda,g) -> (
     d := sum toList lambda;
     Rf := symmRing(QQ,d);
     f := jacobiTrudi(lambda,Rf);
     plethysm(f,g))


--degree of a polynomial in a SchurRing
degSchurPol = method()
degSchurPol(RingElement) := ps -> (
     tms := listForm ps;
     tms/first/sum//max
     )
---------------------------------------------------------------
-----------End plethysm----------------------------------------
---------------------------------------------------------------


---------------------------------------------------------------
----Transition between various types of symmetric functions----
---------------------------------------------------------------

toSymm = method()
--ps should be an element of a schurRing, R a symmRing
--toSymm returns the symmetric function corresponding to ps

toSymm(RingElement) := (ps) ->
(
     S := ring ps;
     if class S =!= SchurRing then ps else
     (
     R := symmetricRingOf S;
     tms := listForm ps;
     sum apply(tms,(p,a)->(
	       (try b:=jacobiTrudi(p,R) then b else error"Need symmetric ring of higher dimension")*
	       toSymm(lift(a,coefficientRing S))))
     )
)

toSymm(Thing) := (ps) -> ps

mapSymToE = method()
mapSymToE (RingElement) := (f) -> (
     R:=ring f; 
     if R.?mapSymToE then R.mapSymToE f else f
)
mapSymToH = method()
mapSymToH (RingElement) := (f) -> (
     R:=ring f; 
     if R.?mapSymToH then R.mapSymToH f else f
)
mapSymToP = method()
mapSymToP (RingElement) := (f) -> (
     R:=ring f; 
     if R.?mapSymToP then R.mapSymToP f else f
)

toE = method()
--writes a symmetric function in terms of
--elementary symmetric polynomials
--toE (RingElement) := (f) -> (ring f).mapSymToE f
toE (RingElement) := (f) -> (
     R := ring f;
     if class R === SchurRing then toE toSymm f
     else 
     (
	  if not R.?schurLevel then f else
	  if R.schurLevel>1 then terms f/(i->(toE leadCoefficient i*(mapSymToE leadMonomial i)))//sum
	  else mapSymToE f
	  )
     )

toP = method()
--writes a symmetric function in terms of
--power sums
--toP (RingElement) := (f) -> (ring f).mapSymToP f
toP (RingElement) := (f) -> (
     R := ring f;
     if class R === SchurRing then toP toSymm f
     else 
     (
	  if not R.?schurLevel then f else
	  if R.schurLevel>1 then terms f/(i->(toP leadCoefficient i*(mapSymToP leadMonomial i)))//sum
	  else mapSymToP f
	  )
     )

toH = method()
--writes a symmetric function in terms of
--complete symmetric polynomials
--toH (RingElement) := (f) -> (ring f).mapSymToH f
toH (RingElement) := (f) -> (
     R := ring f;
     if class R === SchurRing then toH toSymm f
     else 
     (
	  if not R.?schurLevel then f else
	  if R.schurLevel>1 then terms f/(i->(toH leadCoefficient i*(mapSymToH leadMonomial i)))//sum
	  else mapSymToH f
	  )
     )

leadTermFcn := local leadTermFcn;
retFcn := local retFcn;
mappingFcn := local mappingFcn;

toS = method()
toS(RingElement) := (f) -> (
     R := ring f;
     if (schurLevel R == 0 or class R === SchurRing) then f else
     (
	  S := schurRingOf R;
     	  local hf;
     	  n := R.dim;
     	  d := first degree f;
     	  ngS := numgens S;
     	  mappingFcn = (v) -> (schurRingOf ring v)_{index v-2*(ring v).dim+1};
     	  leadTermFcn = (pl) -> (
     	       R := ring pl;
     	       spl := select(support pl,i->index i<numgens R);
     	       if spl == {} then null else last spl
     	       );
     	  retFcn = (pl) -> toS lift(pl,(coefficientRing ring pl));
     	  recTrans(toH(f))*1_S
	  )
     )

toS(RingElement,SchurRing) := (f, T) ->
(
     fS := toS f;
     dimT := numgens T;
     (listForm fS)/(i-> if #i#0<=dimT then T_(i#0)*i#1 else 0_T)//sum
     )


toS(Thing) := (f) -> f

recTrans = method()
recTrans (RingElement) := (pl) ->
(
     lead := leadTermFcn pl;
     if lead === null then retFcn pl else
     (
	  (ex,coe) := coefficients(pl,Variables=>{lead});
	  ex = flatten entries ex;
	  coe = flatten entries coe;
     	  rez := 0;
	  cdeg := degree(lead,ex#0)+1;
	  for i from 0 to #ex-1 do
	  (
	       fdeg := degree(lead,ex#i);
	       while (cdeg>fdeg+1) do
	       (
		    cdeg = cdeg - 1;
		    rez = rez*mappingFcn(lead);
		    );
	       rez = rez*mappingFcn(lead)+recTrans(coe#i);
	       cdeg = cdeg - 1;
	       );
	  while cdeg>0 do 
	       (
		    cdeg = cdeg - 1;
		    rez = rez*mappingFcn(lead);
		    );
	  rez
     	  )
     )

recTrans(Thing) := p -> p

--------
convolve = method()
convolve(List,ZZ) := (L,conv) -> (
     A := ring L_0;
     toList drop(apply(rawConvolve(L/raw//toSequence, conv), f -> new A from f),1)
     )

PtoE = (m,R) -> (
     n := R.dim;
     A := R.symRingForE;
     p2e := prepend(1_A, for i from 1 to n list ((-1)^(i+1) * A_(2*n+i-1)));
     if m>n then p2e = join(p2e,toList((m-n):0_A));
     R.PtoETable = {1_A} | (- convolve(p2e,2));
     )

HtoE = (m,R) -> (
     n := R.dim;
     A := R.symRingForE;
     h2e := prepend(1_A, for i from 1 to n list (-1)^(i+1)*A_(2*n+i-1));
     R.HtoETable = {1_A} | convolve(h2e,0);
     )

HtoP = (m,R) -> (
     n := R.dim;
     A := R.symRingForP;
     h2p := prepend(1_A, for i from 1 to n list A_(2*n+i-1));
     R.HtoPTable = {1_A} | convolve(h2p,1);
     )

EtoP = (m,R) -> (
     n := R.dim;
     A := R.symRingForP;
     e2p := prepend(1_A, for i from 1 to n list (-1)^(i+1)*A_(2*n+i-1));
     R.EtoPTable = {1_A} | convolve(e2p,1);
     )

PtoH = (m,R) -> (
     n := R.dim;
     A := R;
     p2h := prepend(1_A, for i from 1 to n list (- A_(2*n+i-1)));
     R.PtoHTable = {1_A} | convolve(p2h,2);
     )

EtoH = (m,R) -> (
     n := R.dim;
     A := R;
     e2h := prepend(1_A, for i from 1 to n list (-1)^(i+1)*A_(2*n+i-1));
     R.EtoHTable = {1_A} | convolve(e2h,0);
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

centralizerSize = method()
centralizerSize(List) := lambda ->
(
     product for i from 0 to #lambda-1 list((i+1)^(lambda#i)*(lambda#i)!)
     )

ClassFunction = new Type of HashTable

classFunction = method()
classFunction(RingElement) := (f)->
(
     Rf := ring f;

     R :=symmetricRingOf Rf;
     pf := toP f;
     n := R.dim;
     
     if (degree pf)#0 > n then error"Can't interpret ring element as a symmetric function";
     
     (mon,coe) := apply(coefficients pf,i->flatten entries i);
     ch := new MutableHashTable;
     for j from 0 to #mon-1 do
     (
     	  degs := (flatten exponents mon#j)_{(n)..(2*n-1)};
     	  par := multsToSeq(degs);
	  ch#par = lift(coe#j,coefficientRing R) * centralizerSize(degs);
	  );
     new ClassFunction from ch
     )

classFunction(BasicList) := (lambda)->
(
     lam := toList(lambda);
     s := symbol s;
     R := schurRing(QQ,s,sum lam);
     classFunction(R_lam)    
     )

ClassFunction + ClassFunction := (ch1,ch2)->
(
     clSum := new MutableHashTable;
     l1 := sum((keys ch1)#0);
     l2 := sum((keys ch2)#0);
     if l1 != l2 then error("The symmetric functions/characters must have the same degree");
     for i in unique(keys(ch1)|keys(ch2)) do
     	  (
	       a := b := 0;
	       if ch1#?i then a = ch1#i;
	       if ch2#?i then b = ch2#i;
	       if (a+b != 0) then clSum#i = a + b;
	       );
     new ClassFunction from clSum
     )

ZZ * ClassFunction := (n,ch) ->
(
     clProd := new MutableHashTable;
     for i in keys ch do clProd#i = n*ch#i;
     new ClassFunction from clProd     
     )

ClassFunction * ZZ := (ch,n) -> n*ch;

ClassFunction - ClassFunction := (ch1,ch2)-> ch1 + (-1)*ch2;

ClassFunction == ClassFunction := (ch1,ch2) ->
(
     equ := true;
     for i in unique(keys ch1 | keys ch2) do
     	  if not ((not ch1#?i and not ch2#?i) or (ch1#?i and ch2#?i and ch1#i == ch2#i)) then 
     	  (
	       equ = false;
	       break;
	       );
     equ
     )

symmetricFunction = method()
symmetricFunction(ClassFunction,Ring) := (ch,R)->
(
     rez := 0_R;
     n := R.dim;
     for lam in keys ch do
     	  rez = rez + ch#lam * (product for i from 0 to #lam-1 list R_(n-1+lam#i)) / centralizerSize(seqToMults lam);
     rez
     )

scalarProduct = method()
scalarProduct(ClassFunction,ClassFunction) := (ch1,ch2)->
(
     scProd := 0;
     chProd := internalProduct(ch1,ch2);
     for i in keys(chProd) do
     	  scProd = scProd + chProd#i / centralizerSize(seqToMults i);
     scProd
     )

scalarProduct(RingElement,RingElement) := (f1,f2)->
(
     ch1 := classFunction f1;
     ch2 := classFunction f2;
     scalarProduct(ch1,ch2)
     )

internalProduct = method()
ClassFunction * ClassFunction := 
internalProduct(ClassFunction,ClassFunction) := (ch1,ch2)->
(
     iProd := new MutableHashTable;
     l1 := sum((keys ch1)#0);
     l2 := sum((keys ch2)#0);
     if l1 != l2 then error("The symmetric functions/characters must have the same degree");
     for i in keys(ch1) do
     	  if ch2#?i then iProd#i = ch1#i * ch2#i;
     new ClassFunction from iProd
     )

internalProduct(RingElement,RingElement) := (f1,f2)->
(
     R2 := ring f2;
     R := local R;
     issy := false;
     if (class R2 =!= SchurRing) then issy = true;
     R = symmetricRingOf ring f2;
     ch1 := classFunction f1;
     ch2 := classFunction f2;
     rez := symmetricFunction(internalProduct(ch1,ch2),R);
     if issy then rez else
     toS rez
     )


chi(BasicList,BasicList) := (lambda, rho) ->
(
     la := toList lambda;
     rh := toList rho;
     ll := sum la;
     if ll != sum(rh) then error"Partitions must have the same size.";
     R := symmRing(QQ,ll);
     sl := jacobiTrudi(la,R);
     pr := 1_R;
     for i from 0 to #rh-1 do pr = pr * R_(ll-1+rh#i);
     scalarProduct(sl,pr)
     )

---------------------------------------------------------------
--------------End characters-----------------------------------
---------------------------------------------------------------

---------------------------------------------------------------
-----------Partitions-related functions------------------------
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

partitions(Set,BasicList) := (S,L)->
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

--------end generate partitions

---------------------------------------------------------------
--------End partitions-related functions-----------------------
---------------------------------------------------------------


---------------------------------------------------------------
--------Old stuff----------------------------------------------
---------------------------------------------------------------
{*
restart
loadPackage"SchurRings"
----wedge powers over GL(V) x GL(W)
S = schurRing(a,5)
T = schurRing(b,5)
cauchy(3,a_{1},b_{1})
wedge(2,{(a_{1},b_{1}),(a_{3}+a_{2,1},b_{2,2})})
wedge(2,{(a_{1},b_{1}),(a_{1},b_{1})})

r = 3
L = {(a_{1},b_{1}), (a_{3}+a_{2,1},b_{2,2})}

----end wedge powers
*}

exteriorPower (ZZ,RingElement) := opts -> (r,rep) ->
(
     plethysm(splice{r:1},rep)
     )

symmetricPower (ZZ,RingElement) := (r,rep) ->
(
     plethysm({r},rep)
     )

{*cauchy := method(Options => {SymmOrSkew => Symmetric}) --Symmetric, Skewsymmetric
cauchy(ZZ,RingElement,RingElement) := opts -> (i,f,g) -> (
     -- f and g are elements of Schur rings (possibly different)
     -- compute the i th exterior power of the representation f ** g
     P := partitions i;
     result := apply(P, lambda -> (
	       (
		   a := plethysm(lambda,f);
		   if a == 0 then null
		   else (
			b := plethysm(if opts.SymmOrSkew == Symmetric then lambda else conjugate lambda, g);
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
     -- L is a list of lists of (f,g), f,g both in Schur/symmetric rings.
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

wedge = method(Options => options cauchy) 
wedge(List,List) := opts -> (C,L) -> (
     -- C is a composition of 0..n-1, n == #L
     -- form the product of the exterior powers of the corresponding representations.
     result := {}; -- each entry will be of the form (f,g)
     C0 := positions(C, x -> x =!= 0);
     wedgeL := apply(C0, i -> cauchy(C#i,L#i#0,L#i#1,opts));
     pairProduct wedgeL
     )

wedge(ZZ,List) := opts -> (r,L) -> (
     -- r is an integer >= 1
     -- L is a list of pairs (f,g), f,g are in (possibly different) Schur rings.
     -- returns wedge(r)(L), as a sum of representations of GL(m) x GL(n)
     n := #L;
     p := compositions1(r,n);
     flatten apply(p, x -> wedge(x,L,opts))
     )
--this computes the r-th wedge power of the direct sum of
--V_i\tensor W_i where V_i, W_i are GL(V) and GL(W) (virtual) modules
--corresponding to pairs of (virtual) characters (f_i,g_i)
preBott = method()
preBott(ZZ,List) := (i,L) -> (
     R1 := ring L#0#0;
     R2 := ring L#0#1;
     dimQ := numgens R1; -- for general bundles we will need to know the ranks concerned
     dimR := numgens R2;
     x := flatten wedge(i,L);
--     x = apply(x, x0 -> (toS x0#0, toS x0#1)); --x is already an S-function
     B := new MutableHashTable;
     for uv from 0 to #x-1 do
     (
	       (u,v) := x#uv;
     	       (uPar,uCoe) := coefficients u;
	       uPar = apply(flatten entries uPar,j->last j);
	       uCoe = apply(flatten entries uCoe,j->lift(j,coefficientRing R1));
     	       (vPar,vCoe) := coefficients v;
	       vPar = apply(flatten entries vPar,j->last j);
	       vCoe = apply(flatten entries vCoe,j->lift(j,coefficientRing R2));
     	       lu := #uPar-1;lv := #vPar-1;
	       for j from 0 to lu do
	       	    for k from 0 to lv do
		    (
     	       	    	 pQ := value toString uPar#j; --partitions
			 pR := value toString vPar#k; --partitions			 
  		       	 if #pQ < dimQ then
			    pQ = join(pQ,toList((dimQ-#pQ):0));
			 if #pR < dimR then
			    pR = join(pR,toList((dimR-#pR):0));
			 b := join(pQ,pR);
			 c := uCoe#j * vCoe#k; --coefficients
			 if B#?b then B#b = B#b + c else B#b = c;
			 );
	  );
     B)

bott = method()
bott (List) := (QRreps) -> (
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

doBott = method()
doBott(ZZ,HashTable) := (nwedges,B) -> (
     -- B is the output of preBott
     kB := keys B;
     if kB == {} then {}
     else
     (
     s := symbol s;
     S := schurRing(s,(#(first kB)));
     apply(keys B, x -> (
	       b := bott x;
	       if b === null then null
	       else (
		    glb := b#1;
		    d := B#x * dim s_(b#1);
		    (b#0, nwedges - b#0, b#1, B#x, d))))))

--b#0 -> which cohomology is nonzero
--nwedges -> which wedge power we're taking
--b#1 -> partition corresponding to the Schur functor representing the global sections of the pushed forward bundle
--d -> dimension 
weyman = method()
weyman (ZZ,List) := (i,L) -> (
     B := preBott(i,L);
     doBott(i,B))
*}

--------------------------------
-- Dimension -------------------
--------------------------------
-- Function to compute the dimension of a Schur module

hooklengths = (lambda) -> (
     mu := conjugate lambda;
     product for i from 0 to #lambda-1 list (
	  product for j from 0 to lambda#i-1 list (
	       lambda#i + mu#j - i - j -1
	       ))
     )

dimSchur = method()
dimSchur(Thing,List) := (n,lambda) -> dimSchur(n, new Partition from lambda)
dimSchur(Thing,Partition) := (n, lambda) -> (
     -- lambda is a list {a0,a1,...,a(r-1)}, a0 >= a1 >= ... >= a(r-1) > 0
     -- n can be a number or a symbol
     powers := new MutableList from toList(lambda#0 + #lambda - 1 : 0);
     base := 1 - #lambda;
     for i from 0 to #lambda-1 do
       for j from 0 to lambda#i-1 do
       	    powers#(j-i-base) = powers#(j-i-base) + 1;
     if not instance(n,ZZ) then n = hold n;
     num := product for s from 0 to #powers-1 list (n + (base+s))^(powers#s);
     -- now get the hook lengths
     answer := num/hooklengths lambda;
     if instance(answer,QQ) then lift(answer,ZZ) else answer
     )
dimSchur(Thing,RingElement) := (n, F) -> (
     -- assumption: F is an element in a SchurRing
     L := listForm F;
     sum apply(L, p -> (
	       lambda := new Partition from p#0;
	       if p#1 == 1 then dimSchur(n,lambda) else p#1 * dimSchur(n,lambda)))
     )
dimSchur(List,RingElement) := (ns, F) -> (
     -- assumption: F is an element in a SchurRing
     L := listForm F;
     n := ns#0;
     lev := schurLevel ring F;
     if lev =!= #ns then error ("expected Schur ring of level "|lev);
     if lev > 1 then (
	  n1 := drop(ns,1);
	  L = apply(L, p -> (p#0, dimSchur(n1,p#1)));
	  );
     sum apply(L, p -> (
	       lambda := new Partition from p#0;
	       if p#1 === 1 then dimSchur(n,lambda) else p#1 * dimSchur(n,lambda)))
     )
dimSchur(RingElement) := (F) -> (
     schurdims := (S) -> (
	  if schurLevel S === 0 then {}
	  else prepend(numgens S, schurdims coefficientRing S));
     ns := schurdims ring F;
     if any(ns, i -> not instance(i,ZZ))
     then error "expected finitely generated Schur rings";
     dimSchur(ns,F)
     )
---------------------------------------------------------------
--------End old stuff----------------------------------------------
---------------------------------------------------------------

beginDocumentation()

--undocumented (wedge,List,List)
undocumented {EorH, Schur}

document {
     Key => "SchurRings",
     Headline => "rings representing irreducible representations of GL(n)",
     "This package makes computations in the representation rings of general linear groups and symmetric groups possible.",
     PARA{},
     "Given a positive integer ", TT "n", ", 
     we may define a polynomial ring over ", TO "ZZ", " (or ", TO "QQ", ") in ", TT "n", " variables, whose
     monomials correspond to the irreducible representations of GL(n), and where 
     multiplication is given by the decomposition of the tensor product of representations",
     PARA{},
     "We create such a ring in Macaulay2 using the ", TO schurRing, " function:",
     EXAMPLE "R = schurRing(QQ,s,4);",
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
     Key => {schurRing,(schurRing,Ring,Symbol,ZZ),(schurRing,Ring,Thing,ZZ)},
     Headline => "Make a Schur ring",
     TT "schurRing(s,n)", " -- creates a Schur ring of degree n with variables based on the symbol s",
     PARA{"This is the representation ring for the general linear group of ", TT "n", " by ", TT "n", " matrices."},
     PARA{"If ", TT "s", " is already assigned a values as a variable in a ring, its base symbol will be used,
	  if it is possible to determine."},
     SeeAlso => {"SchurRing", "symmRing"}}

document {
     Key => {SchurRing, (coefficientRing, SchurRing)},
     Headline => "the class of all Schur rings",
     "A Schur ring is the representation ring for the general linear group of 
     n by n matrices, and one can be constructed with ", TO schurRing, ".",
     EXAMPLE "R = schurRing(QQ, s, 4)",
     "The element corresponding to the Young diagram ", TT "{3,2,1}", " is
     obtained as follows.",
     EXAMPLE "s_{3,2,1}",
     "The dimension of the underlying virtual representation can be obtained
     with ", TO "dim", ".",
     EXAMPLE "dim s_{3,2,1}",
     "Multiplication in the ring comes from tensor product of representations.",
     EXAMPLE "s_{3,2,1} * s_{1,1}",
     SeeAlso => {schurRing}}

document {
     Key => {SchurRingIndexedVariableTable,(symbol _,SchurRingIndexedVariableTable,Thing)},
     "This class is used as part of the implementation of a type of indexed variable used just for Schur rings.",
     SeeAlso => { IndexedVariableTable }
     }

doc ///
Key
  symmRing
Headline
  Make a Symmetric ring
Usage
  symmRing n
Inputs
  n:ZZ
Description
  Text

    {\tt symmRing n} creates a Symmetric ring of dimension {\tt n}.
    This is the subring of the ring of symmetric functions consisting
    of polynomials in the first {\tt n} elementary (or complete, or power sum)
    symmetric functions.

SeeAlso
  SchurRing
///

doc ///
   Key
     toS
   Headline 
     Schur (s-) basis representation
   Description
      Text
      
     	  Given a symmetric function {\tt f}, the function 
	  {\tt toS} yields a representation of {\tt f} as a linear
	  combination of Schur functions. 
      
      Example
      	  R = symmRing(QQ,6);
	  toS(h_3*e_3)
      
      Text	  
	
	  If a {\tt SchurRing S} is provided as input, then one interprets
	  the input function {\tt f} as a (virtual) character of a certain general linear
	  group, and the output as a representation of {\tt f} as a sum of characters.
      
      Example
      	  R = symmRing(QQ,6);
	  toS(h_3*e_3)
      
      Text
      
      	  One can notice that the outputs of two examples above 
	  do not coincide. This is because the former example gives
	  an actual symmetric function, while the latter gives an 
	  element of the representation ring of GL_3, which is a quotient
	  of the ring of symmetric functions.
   SeeAlso
     toH
     toE
     toP
///

doc ///
   Key
     (toS,RingElement)
   Headline
     Represents a symmetric function in the s-basis
   Usage
     fs = toS f
   Inputs
     f:RingElement
       element of a Symmetric ring
   Outputs
     fs:RingElement
        element of a Schur ring
   Description
      Text

        The input function {\tt f} should be interpreted as a symmetric
	function, as well as the output, which is an element of the Schur
	ring {\tt R.Schur} attached to the Symmetric ring {\tt R} of {\tt f}.

      Example
        R = symmRing(QQ,4);
        toS(e_1*h_2+p_3)

      Text

        An error is returned if the degree of the input function {\tt f}
	is larger than the dimension of the Symmetric ring of {\tt f}.
///

doc ///
  Key
    toE
  Headline
     Elementary symmetric (e-) basis representation
  Description
      Text

          Given a symmetric function {\tt f}, the function 
          {\tt toE} yields a representation of {\tt f} as a polynomial
	  in the elementary symmetric functions.

      Example
      	  R = symmRing(QQ,7);
	  toE(h_3*e_3+p_2*h_5+h_1^2*p_3)
      
      Text	  
	
	  The symmetric function {\tt f} need not be an element of a Symmetric
	  ring. It may be an element of a Schur ring, in which case one needs
	  to specify a Symmetric ring to carry the e-representation of {\tt f}.
      
      Example
      	  R = symmRing(QQ,9);
	  S = schurRingOf R
	  toE(S_{3,2,1}*S_{2}+S_{4,2})
  SeeAlso
    toH
    toS
    toP
///

doc ///
   Key
     (toE,RingElement)
   Headline
     Represents a symmetric function in the e-basis
   Usage
     fe = toE f
   Inputs
     f:RingElement
       element of a Symmetric ring
   Outputs
     fe:RingElement
        element of a Symmetric ring
   Description
      Text

        If the input {\tt f} is a symmetric function, element of a 
	Symmetric ring {\tt R}, then the output {\tt fe} is
	the representation of {\tt f} as a polynomial in the 
	elementary symmetric functions in {\tt R}.

      Example
        R = symmRing(QQ,4);
        toE(e_1*h_2+p_3)
///

doc ///
  Key
    toH
  Headline
     Complete symmetric (h-) basis representation
  Description
      Text

          Given a symmetric function {\tt f}, the function 
          {\tt toH} yields a representation of {\tt f} as a polynomial
	  in the complete symmetric functions.

      Example
      	  R = symmRing(QQ,7);
	  toH(h_3*e_3+p_2*h_5+h_1^2*p_3)
      
      Text	  
	
	  The symmetric function {\tt f} need not be an element of a Symmetric
	  ring. It may be an element of a Schur ring, in which case one needs
	  to specify a Symmetric ring to carry the h-representation of {\tt f}.
      
      Example
      	  R = symmRing(QQ,9);
	  S = schurRingOf R
	  toH(S_{3,2,1}*S_{2}+S_{4,2})
  SeeAlso
    toE
    toS
    toP
///

doc ///
   Key
     (toH,RingElement)
   Headline
     Represents a symmetric function in the h-basis
   Usage
     fh = toH f
   Inputs
     f:RingElement
       element of a Symmetric ring
   Outputs
     fh:RingElement
        element of a Symmetric ring
   Description
      Text

        If the input {\tt f} is a symmetric function, element of a 
	Symmetric ring {\tt R}, then the output {\tt fh} is
	the representation of {\tt f} as a polynomial in the 
	complete symmetric functions in {\tt R}.

      Example
        R = symmRing(QQ,4);
        toH(e_1*h_2+p_3)
///

doc ///
  Key
    toP
  Headline
     Power-sum (p-) basis representation
  Description
      Text

          Given a symmetric function {\tt f}, the function 
          {\tt toP} yields a representation of {\tt f} as a polynomial
	  in the power-sum symmetric functions.

      Example
      	  R = symmRing(QQ,7);
	  toP(2*(e_1^2-e_2))

      Text	  
	
	  The symmetric function {\tt f} need not be an element of a Symmetric
	  ring. It may be an element of a Schur ring, in which case one needs
	  to specify a Symmetric ring to carry the p-representation of {\tt f}.
      
      Example
      	  R = symmRing(QQ,6);
	  S = schurRingOf R
	  toP(2*S_{3}-S_{2,1})
  SeeAlso
    toH
    toS
    toE
///

doc ///
   Key
     (toP,RingElement)
   Headline
     Represents a symmetric function in the p-basis
   Usage
     fp = toP f
   Inputs
     f:RingElement
       element of a Symmetric ring
   Outputs
     fp:RingElement
        element of a Symmetric ring
   Description
      Text

        If the input {\tt f} is a symmetric function, element of a 
	Symmetric ring {\tt R}, then the output {\tt fp} is
	the representation of {\tt f} as a polynomial in the 
	power-sum symmetric functions in {\tt R}.

      Example
        R = symmRing(QQ,4);
        toP(e_1*h_2+p_3)
///

doc ///
Key
  jacobiTrudi
  (jacobiTrudi,BasicList,Ring)
Headline
  Jacobi-Trudi determinant
Usage
  f = jacobiTrudi(lambda,R)
Inputs
  lambda:BasicList
         a nonincreasing list of integers, or a partition
  R:Ring
    a Symmetric ring
Outputs
  f:RingElement
    an element of a Symmetric ring
Description
  Text
  
    Given a partition {\tt lambda} and Symmetric ring {\tt R},
    the method evaluates the Jacobi-Trudi determinant corresponding
    to the partition {\tt lambda}, yielding a representation of
    the Schur function {\tt s_{lambda}} as a symmetric function
    in {\tt R}. The default option is to represent this symmetric
    function in terms of {\tt h-}polynomials.
  
  Example
    R = symmRing(QQ,10);
    jacobiTrudi({3,2,2,1},R,EorH => "E")
    jacobiTrudi(new Partition from {4,4,1},R)
    toS oo
///

doc///
   Key
     [jacobiTrudi,EorH]
   Headline
     e- or h- representation of Jacobi-Trudi determinant
   Usage
     EorH => s
   Inputs
     s:String
       either "E" or "H"
   Description
     Text
       This option allows one to choose between evaluating the
       Jacobi-Trudi determinant in the {\tt e}- or {\tt h}- basis.
       If the length of the conjugate partition {\tt lambda'} is
       smaller than the length of {\tt lambda}, then it is
       computationally less expensive to set the option {\tt EorH}
       to {\tt E}. Otherwise, the default value {\tt H} is more
       efficient.
///   

doc///
   Key
     [jacobiTrudi,Memoize]
   Headline
     Store values of the jacobiTrudi function.
   Usage
     Memoize => b
   Inputs
     b:Boolean
   Description
     Text
     
       If the option is set to {\tt true} then all the values of the jacobiTrudi 
       function that are computed are recorded into a special hash table attached
       to the symmetric ring inside which the computations are done.
///   

doc ///
Key
  plethysm
  (plethysm,RingElement,RingElement)
Headline
  Plethystic composition of symmetric functions/characters
Usage
  pl = plethysm(f,g)
Inputs
  f:RingElement
    element of Symmetric ring or Schur ring
  g:RingElement
    element of Symmetric ring or Schur ring
Outputs
  pl:RingElement
     element of Symmetric ring or Schur ring
Description
  Text
    Given two symmetric functions (or virtual characters of a general
    linear group) {\tt f} and {\tt g}, the method computes their
    plethystic composition. If {\tt g} is an element of a symmetric
    ring, then both {\tt f,g} are regarded as symmetric functions.
    Otherwise they are considered to be virtual characters. The result
    of the composition of {\tt f} and {\tt g} will be an element of
    the ring of {\tt g}.
    
  Example
    R = symmRing(QQ,10);
    p = plethysm(h_2,h_5)
    toS p
    S = schurRing(QQ,q,3);
    plethysm(h_2,q_{2,1})
    plethysm(q_{2,1},q_{2,1})
    
  Text
    
    An error is returned if {\tt g} is an element of a Symmetric ring {\tt R}
    and the product of the degrees of {\tt f} and {\tt g} is
    smaller than the dimension of {\tt R}.
///

doc ///
Key
  (plethysm,BasicList,RingElement)
Headline
  Plethystic composition of Schur function and symmetric function/character
Usage
  pl = plethysm(lambda,g)
Inputs
  lambda:BasicList
         nonincreasing sequence of positive integers, or partition
  g:RingElement
    element of Symmetric ring or Schur ring
Outputs
  pl:RingElement
     element of Symmetric ring or Schur ring
Description
  Text
    
    The method computes the plethystic composition of a Schur function
    corresponding to a partition {\tt lambda} and a symmetric function 
    or virtual character. This is the most commonly used form of plethysm.

  Example
    R = symmRing(QQ,6)
    S = schurRing(QQ,q,3)
    plethysm({2,1},e_2)
    plethysm({2,1,1},q_{1,1}) 
///

doc ///
  Key
    (partitions,Set,BasicList)
  Headline
    Partitions of a set
  Usage
    par = partitions(S,L)
  Inputs
    S:Set
    L:BasicList
      a nonincreasing list of integers, or a partition
  Outputs
    par:List
  Description
    Text

      Given a set {\tt S} and a partition {\tt L=\{l_1\geq l_2\cdots\}}, the method
      returns the list of partitions of the set {\tt S} of type
      {\tt L}, i.e. representations of {\tt S} as {\tt S=S_1\cup S_2\cup\cdots}, where
      the {\tt S_i}'s are disjoint subsets of {\tt S} having {\tt t_i} elements.

    Example
      partitions(set{1,2,3,4},{2,1,1})
      partitions(set{a,b,c,d,e},new Partition from {3,2})
///  


doc ///
 Key
  (chi,BasicList,BasicList)
 Headline
  Irreducible character of symmetric group
Usage
  v = chi(lambda,rho)
Inputs
  lambda:BasicList
   	 a nondecreasing list of positive integers, or a partition
  rho:BasicList
      a nondecreasing list of positive integers, or a partition
Outputs
  v:QQ
Description
  Text

    Given two partitions {\tt lambda} and {\tt rho} of the integer {\tt N}, this method
    computes the value of the irreducible character of the symmetric group
    corresponding to the partition {\tt lambda} evaluated on
    any permutation of cycle-type {\tt rho}.

    The character of the trivial representation takes the value
    1 on any permutation:
  
  Example
    chi({4},{2,1,1})
    
  Text
  
    The character of the sign representation takes the value -1 on
    a cycle of length 4:
  
  Example
    chi({1,1,1,1},{4})
SeeAlso
   symmetricFunction
   classFunction
///

doc ///
Key
  symmetricFunction
  (symmetricFunction,ClassFunction,Ring)
Headline
  Converts virtual character to symmetric function
Usage
  f = symmetricFunction(ch,R)
Inputs
  ch:ClassFunction
  R:Ring
    a Symmetric ring
Outputs
  f:RingElement
    element of a Symmetric ring
Description
  Text
    Given a virtual character {\tt ch} of a
    symmetric group, and given a Symmetric ring {\tt R}, 
    the method computes the corresponding symmetric function
    as an element of {\tt R}.
    
  Example
    R = symmRing(QQ,4);
    symmetricFunction(new ClassFunction from {{1,1,1,1}=>2},R)
SeeAlso
  classFunction
  chi
///

doc ///
Key
  classFunction
  (classFunction,RingElement)
Headline
  Converts symmetric function to virtual character
Usage
  ch = classFunction(f)
Inputs
  f:RingElement
    element of a Symmetric ring
Outputs
  ch:ClassFunction
Description
  Text
    Given a symmetric function {\tt f}, homogeneous of degree {\tt N}, 
    the method computes the corresponding virtual character
    of the symmetric group {\tt S_N}.
    
    The character of the standard representation of {\tt S_5} is
    
  Example
    R = symmRing(QQ,5);
    classFunction(jacobiTrudi({4,1},R))
  Text

    The character of the second exterior power of the standard representation of {\tt S_5} is
    
  Example
    R = symmRing(QQ,5);
    classFunction(jacobiTrudi({3,1,1},R))
SeeAlso
  symmetricFunction
  chi
///

doc ///
Key
  scalarProduct
Headline
  Standard pairing on symmetric functions/class functions
Description
  Text
  
    This method computes the standard scalar product on the ring {\tt \Lambda}
    of symmetric functions. One way to define this product is by imposing
    that the collection of Schur functions {\tt s_{\lambda}} form
    an orthonormal basis.
    
    Alternatively, by the correspondence between symmetric functions
    and virtual characters of symmetric groups, this scalar product
    coincides with the standard scalar product on class functions.

    The number of standard tableaux of shape {\tt \{4,3,2,1\}} is:
  
  Example
    R = symmRing(QQ,10);
    S = schurRing(QQ,s,10);
    scalarProduct(h_1^10,s_{4,3,2,1})
SeeAlso
  internalProduct
///

doc ///
Key
  (scalarProduct,RingElement,RingElement)
Headline
  Standard scalar product of symmetric functions
Usage
  sp = scalarProduct(f1,f2)
Inputs
  f1:RingElement
     element of a Symmetric Ring
  f2:RingElement
     element of a Symmetric Ring
Outputs
  sp:QQ
Description
  Text
    
    Given symmetric functions {\tt f1} and {\tt f2}, the method
    computes the standard pairing between {\tt f1} and {\tt f2}.
    
  Example
    R = symmRing(QQ,5);
    S = schurRingOf R
    scalarProduct(h_5,p_5)
    scalarProduct(S_{4,1},p_5)
  
  Text
  
    Indeed, the coefficients of {\tt s_5} and {\tt s_{4,1}} in the
    s-basis expansion of {\tt h_5} are as computed above:
    
  Example
    R = symmRing(QQ,5);
    toS p_5
///

doc ///
Key
  (scalarProduct,ClassFunction,ClassFunction)
Headline
  Standard scalar product of class functions
Usage
  sp = scalarProduct(ch1,ch2)
Inputs
  ch1:ClassFunction
  ch2:ClassFunction
Outputs
  sp:QQ
Description
  Text
    
    Given virtual characters {\tt ch1} and {\tt ch2}, the method
    computes the standard pairing between {\tt ch1} and {\tt ch2}.
    
  Example
    ch1 = new ClassFunction from {{3,2} => 2, {2,2,1} => -2, {3,1,1} => 2, {5} => 1};
    ch2 = new ClassFunction from {{2,2,1} => -2, {5} => 1, {1,1,1,1,1} => 5, {3,2} => 3, {4,1} => -2};
    scalarProduct(ch1,ch2)
///

doc ///
Key
  internalProduct
Headline
  Internal product of symmetric functions/class functions
Description
  Text
  
    This method computes the internal (Kronecker) product of two homogeneous symmetric
    functions of the same degree. If we think of these functions as being
    virtual characters of some symmetric group, then their internal product
    is just the character of the tensor product of the corresponding virtual
    representations.

    The complete symmetric function of degree {\tt n} corresponds
    to the trivial {\tt S_n}-representation and is therefore
    the unit of the representation ring of {\tt S_n}:
  
  Example
    R = symmRing(QQ,5);
    S = schurRing(QQ,s,3);
    internalProduct(h_3,s_{2,1})
  Text
  
    The square of the sign representation is the trivial representation:
    
  Example
    R = symmRing(QQ,5);
    toH internalProduct(e_3,e_3)
SeeAlso
  scalarProduct
///

doc ///
Key
  (internalProduct,RingElement,RingElement)
Headline
  Kronecker product of symmetric functions
Usage
  ip = internalProduct(f1,f2)
Inputs
  f1:RingElement
     element of a Symmetric ring or a Schur ring
  f2:RingElement
     element of a Symmetric ring or a Schur ring
Outputs
  ip:Ring
     a Symmetric ring or a Schur Ring
Description
  Text
    
    Given symmetric functions {\tt f1} and {\tt f2}, the method
    computes the Kronecker product {\tt ip} between {\tt f1} and {\tt f2}.
    The output {\tt ip} is an element in the ring of {\tt f2}.
    
  Example
     R = symmRing(QQ,6);
     S = schurRing(QQ,s,6);
     internalProduct(s_{3},e_3)
     Q = schurRing(QQ,q,6);
     internalProduct(s_{3,3},q_{4,2})   
  Text
   
    An error is returned if {\tt f1} and {\tt f2} don't have the
    same degree.
///

doc ///
Key
  (internalProduct,ClassFunction,ClassFunction)
Headline
  Tensor product of virtual representations
Usage
  ip = internalProduct(ch1,ch2)
Inputs
  ch1:ClassFunction
  ch2:ClassFunction
Outputs
  ip:ClassFunction
Description
  Text
    
    Given virtual characters {\tt ch1} and {\tt ch2}, the method
    computes the character of the tensor product of corresponding
    virtual representations of the symmetric group.
    
  Example
    ch1 = new ClassFunction from {{4,4} => 2, {8} => -1, {5,2,1} => 2, {3,2,2,1} => 1};
    ch2 = new ClassFunction from {{2,2,2,2} => -4, {5,2,1} => 1, {3,2,2,1} => 3};
    internalProduct(ch1,ch2)
    ch1 * ch2
///

doc ///
Key
  centralizerSize
  (centralizerSize,List)
Headline 
  Size of the centralizer of a permutation
Usage 
  n = centralizerSize(rho)
Inputs 
  rho:List
Outputs 
  n:ZZ
Description
  Text

    {\tt rho} is a list representing the cycle type of some permutation: the i-th entry in {\tt rho} is the number of cycles of length i of the permutation.
    The output of the function {\tt centralizerSize} is the size of the centralizer in the symmetric group of any permutation of cycle type {\tt rho}. The cycle type {\tt rho}
    corresponds to a partition {\tt lambda}, in which case {\tt centralizerSize(rho)} is also the value of the square norm of the symmetric function {\tt p_{lambda}}.

  Example
    centralizerSize{1,1,1}
    R = symmRing(QQ,6);
    u = p_1 * p_2 * p_3;
    scalarProduct(u,u)
///

doc ///
  Key
    Memoize
  Headline
    Record values of the jacobiTrudi function
  Description
    Text
    
      This is an optional argument for the @TO jacobiTrudi@
      and @TO toS@ methods, allowing one to store the values
      of the @TO jacobiTrudi@ function in order to speed up
      computations.
///

--------------------
-- test Jacobi-Trudi
--------------------
TEST ///
E = symmRing(QQ,5)
f = jacobiTrudi({4,1},E)
g = toS f
G = ring g
assert (g == G_{4,1})
///

TEST ///
E = symmRing(QQ,5)
f = jacobiTrudi({2,1},E)
g = toS f
G = ring g
assert (g == G_{2,1})
///

TEST ///
E = symmRing(QQ,13)
f = jacobiTrudi({7,4,2},E)
g = toS f
G = ring g
assert (toS f == G_{7,4,2})
///

TEST ///
P = symmRing(QQ,6)
f = toS plethysm(jacobiTrudi({2},P), jacobiTrudi({2},P))
G = ring f
assert(f == G_{4}+G_{2,2})
///

TEST ///
Q = symmRing(QQ,5)
--S = schurRing(QQ,q,4)
S = schurRingOf Q
f = toS(plethysm(jacobiTrudi({3},Q), jacobiTrudi({2},Q)))
--assert(dim f == 220)
assert(dim(4,f) == 220)
///
------------------------
-- end test Jacobi-Trudi
------------------------

------------------------
-- test of plethysm, toS
------------------------
TEST ///
R = symmRing(QQ,4)
pl = plethysm({1,1},jacobiTrudi({2},R))
G = schurRingOf ring pl
assert(toS pl == G_{3,1})
///

TEST ///
R = symmRing(QQ,12)
pl = plethysm({1,1,1},jacobiTrudi({4},R))
assert(#listForm(toS pl) == 7)
///

TEST ///
R = symmRing(QQ, 9)
S = schurRing(QQ,q,3)
pl = plethysm(h_3,q_{2,1})
assert (dim(pl) == 120)
///

TEST ///
R = symmRing(QQ,3)
--S = schurRing(QQ,s,3)
S = schurRingOf R
assert(toS(plethysm(h_3,e_3)) == S_{3,3,3})
///

TEST ///
S = schurRing(QQ,q,4)
assert(plethysm(q_{2,1},q_{1,1,1}) == q_{3,3,2,1})
///

TEST ///
R = symmRing(QQ, 12)
f = e_4
lambda = new Partition from {3}
assert(plethysm(lambda,f) == plethysm(h_3,e_4))
///

TEST ///
schurRing(QQ,s,2)
assert(dim(plethysm(s_{2,1}+s_{3},s_{3})) == 40)
///

TEST ///
R = symmRing(QQ,20)
assert(#listForm(toS plethysm(h_5,h_4)) == 95)
///


TEST ///
R = symmRing(QQ, 10)
--S = schurRing(QQ,o,5)
S = schurRingOf R
sch = toS(plethysm({2,1},h_3))
--assert(dim sch == 14770)
assert(dim(5,sch) == 14280)
/// --maybe this is wrong??

----------------------------
-- end test of plethysm, toS
----------------------------

--------------------------------------------------------------
----- test characters of symmetric groups, scalarProd, intProd
--------------------------------------------------------------
TEST ///
assert(chi({2,1,1,1},{2,1,1,1}) == -2)
assert(chi({3,1,1},{1,1,1,1,1}) == 6)
assert(chi({3,2},{3,1,1}) == -1)
assert(chi({2,2,1},{3,1,1}) == -1)
assert(chi({3,1,1},{2,2,1}) == -2)
///

TEST ///
R = symmRing(QQ,20)
S = schurRing(QQ,o,20)
assert(scalarProduct(o_{6,4,3,2,1},jacobiTrudi({3,3,3},symmetricRingOf S)*toP(o_{4,2,1})) == 2)
assert(scalarProduct(jacobiTrudi({6,4,3,2,1},R),jacobiTrudi({4,3,3,3,2,1},R)) == 0)
assert(scalarProduct(jacobiTrudi({6,4,3,2,1},R),o_{4,3,3,3,2,1}) == 0)
///

TEST ///
R = symmRing(QQ,5)
A = schurRing(QQ,a,4)
assert(internalProduct(e_2+h_2,a_{2}) == a_{2}+a_{1,1})
assert(toE internalProduct(a_{2},e_2+h_2) == toE p_1^2)
assert(dim internalProduct(a_{2,1}*a_{1},a_{2,2}) == 176)
///


TEST ///
R = symmRing(QQ,10)
ch1 = new ClassFunction from {{4,4} => 2, {8} => -1, {5,2,1} => 2, {3,2,2,1} => 1};
ch2 = new ClassFunction from {{2,2,2,2} => -4, {5,2,1} => 1, {3,2,2,1} => 3};
assert(toP symmetricFunction(internalProduct(ch1,ch2),R) == 1/8*p_1*p_2^2*p_3+1/5*p_1*p_2*p_5)
assert(toP symmetricFunction(ch1*ch2,R) == 1/8*p_1*p_2^2*p_3+1/5*p_1*p_2*p_5)
///

TEST ///
R = symmRing(QQ,4)
f = p_2^2
g = (e_2+h_2)^2
ch1 = classFunction(f)
ch2 = classFunction(g)
assert(symmetricFunction(internalProduct(ch1,ch2),R) == 0)
assert(internalProduct(f,g) == 0)
///
----------------------------------------------------------------
--- end test characters of symmetric groups, scalarProd, intProd
----------------------------------------------------------------

---------------------------
--- test toS, toP, toE, toH
---------------------------
TEST ///
R = symmRing(QQ,6)
assert(toE(toS(e_1*e_2*e_3)) == e_1*e_2*e_3)
///

TEST ///
R = symmRing(QQ,5)
S = schurRing(QQ,q,3)
assert(toE(q_{2}) + e_2 == e_1^2)
///

TEST///
R = symmRing(QQ, 4)
assert(toP toE toH toE toH toP toE toE toP toH (p_1+p_2+p_3) == p_1+p_2+p_3)
///

TEST ///
R = symmRing(QQ,6)
S = schurRingOf R
toSf = map(S, R, apply(gens R, x -> toS(x)))
assert(toSf(e_1*e_2*e_3) == S_(3,2,1)+S_(3,1,1,1)+S_(2,2,2)+2*S_(2,2,1,1)+2*S_(2,1,1,1,1)+S_(1,1,1,1,1,1))
assert(toSf(h_1*h_2*h_3) == S_{1}*S_{2}*S_{3})
///

TEST ///
R = symmRing(QQ,7)
assert(toH toP toE (toS (jacobiTrudi({2,1},R))^2) == (h_1*h_2-h_3)^2)
///
-------------------------------
--- end test toS, toP, toE, toH
-------------------------------

end

restart
uninstallPackage "SchurRings"
installPackage "SchurRings"
check SchurRings
viewHelp SchurRings
--print docTemplate
end

-------
restart
loadPackage"SchurRings"
A = schurRing(a,2)
B = schurRing(b,2)
L = {(1_A,b_{3,2})}
L = {(a_{3,2},b_{6,1})}
i = 1

select(weyman(i,L),x->x =!= null)
end
-------

S = schurRing(s,12)
time F = s_{17,7,7,7,3,3,1} * s_{10,5,1};
size F
T = schurRing2(ZZ,t,12)
T = schurRing2(ZZ,t)
time G = t_{17,7,7,7,3,3,1} * t_{10,5,1};
lisF = hashTable listForm F;
lisG = hashTable listForm G;
assert(lisF === lisG)

restart
loadPackage "SchurRings"
S = schurRing(s,12)
time F = s_{20,20,17,7,7,7,3,3,1} * s_{10,5,1};
size F
T = schurRing2(ZZ,t,20)
time G = t_{20,20,17,7,7,7,3,3,1} * t_{10,5,1};
time G2 = t_{10,5,1} * t_{20,20,17,7,7,7,3,3,1};
lisF = hashTable listForm F;
lisG = hashTable listForm G;
lisG2 = hashTable listForm G2;
assert(lisF === lisG)
assert(lisF === lisG2)
U = schurRing2(ZZ,u)
time H = u_{20,20,17,7,7,7,3,3,1} * u_{10,5,1};
time H3 = u_{20,20,17,7,7,7,3,3,1} * u_{10,5,1};
time H2 = u_{10,5,1} * u_{20,20,17,7,7,7,3,3,1};
lisH = hashTable listForm H;
lisH2 = hashTable listForm H2;
assert(lisF === lisH)
assert(lisF === lisH2)

S = schurRing(symbol s, 10)
F = s_{12,3} * s_{12,4};

restart
n = 30
time A = symmRing2(QQ, n)

--A = QQ[h_1..h_n,e_1..e_n,p_1..p_n,MonomialSize=>8]
h2p = prepend(1_A, for i from 1 to n list p_i)
time H2P = convolve(h2p,1);

p2h = prepend(1_A, for i from 1 to n list -h_i)
time P2H = convolve(p2h,2);

e2p = prepend(1_A, for i from 1 to n list ((-1)^(i+1) * p_i))
time E2P = convolve(e2p,1);

p2e = prepend(1_A, for i from 1 to n list ((-1)^(i+1) * e_i))
time P2E = - convolve(p2e,2);

h2e = prepend(1_A, for i from 1 to n list (-1)^(i+1)*e_i)
time H2E = convolve(h2e,0);

e2h = prepend(1_A, for i from 1 to n list (-1)^(i+1)*h_i)
time E2H = convolve(e2h,0);

H2P - for i from 1 to n list toP h_i
P2H - for i from 1 to n list toH p_i
E2P - for i from 1 to n list toP e_i
P2E + for i from 1 to n list toE p_i
H2E - for i from 1 to n list toE h_i
E2H - for i from 1 to n list toH e_i
--------------------------------------------------------------

restart
loadPackage"SchurRings"

S = schurRing(QQ,s,10)
T = schurRing(S,t,10)

symmetricRingOf T

debug SchurRings
f = toSymm S_{2,1}
g = toSymm T_{2,1}
f - g
toS oo

toE s_{2,1}
toE t_{2,1}
toE h_3
toE s_{3}
toH oo
toH s_{3}

plethysm(t_{2},t_{3})
plethysm(t_{2},s_{2})

toE plethysm(t_{2},h_3)
toE plethysm(h_2,t_{2,1})
toS oo
plethysm(t_{2},t_{2,1})
plethysm(s_{2},t_{2,1})


rep = S_{1}*T_{2}+S_{2,1}*T_{1,1}
toSymm rep
toE oo
toP oo
toH oo
toP oo
toS oo
toE oo
toS oo
toH oo

rep = s_{2}*t_{2}

toP S_{2}
toE oo
toH oo
toS oo

plethysm(h_2,S_{3,1})
toH oo
plethysm(S_{2},oo)

R = symmRing(QQ,10)
e_5
toS oo

exteriorPower(2,S_{2}*T_{2}+T_{1})
toE oo
toS oo

exteriorPower(2,T_{2})
plethysm(S_{1,1},T_{2})


restart
loadPackage"SchurRings"

R = schurRing(QQ,a,10)
S = schurRing(R,b,10)
T = schurRing(S,c,10)
g = a_{1}*b_{1}*c_{1}
time plethysm2({2},g)
time plethysm({2},g)

time plethysm2({1,1},a_{1}*c_{1})
time plethysm({1,1},g)

restart
loadPackage"SchurRings"

n = 30
m = 20
time R = symmRing(QQ,n)
time ple = plethysm(h_5,h_6);

time p = toS ple;
size p
p

restart
loadPackage"SchurRings"

n = 6
time R = symmRing(QQ,n)
time ple = plethysm(h_5,h_6);

time toS ple;

restart
loadPackage"SchurRings"

S = schurRing(QQ,s,3,EHPSVariables => {es,hs,ps,s})
T = schurRing(S,t,2)

symmetricPower(3,S_{1}*1_T)
exteriorPower(3,T_{1}*S_{1})

exteriorPower(3,S_{1}+T_{1})
symmetricPower(3,S_{1}+T_{1})


exteriorPower(3,S_{1})
exteriorPower(3,S_{1}*T_{1})
toH oo
toE oo
toP oo
toS oo

viewHelp symmetricPower 

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=SchurRings pre-install"
-- End: