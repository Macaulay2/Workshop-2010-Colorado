-- -*- coding: utf-8 -*-
newPackage(
	"Schubert2",
	AuxiliaryFiles => true,
    	Version => "0.3",
    	Date => "December, 2009",
	Authors => {
	     {Name => "Daniel R. Grayson", Email => "dan@math.uiuc.edu", HomePage => "http://www.math.uiuc.edu/~dan/"},
	     {Name => "Michael E. Stillman", Email => "mike@math.cornell.edu", HomePage => "http://www.math.cornell.edu/People/Faculty/stillman.html"},
	     {Name => "Stein A. Strømme", Email => "stromme@math.uib.no", HomePage => "http://stromme.uib.no/home/" },
	     {Name => "David Eisenbud", Email => "de@msri.org", HomePage => "http://www.msri.org/~de/"},
	     {Name => "Charley Crissman", Email => "charleyc@gmail.com", HomePage => "http://www.berkeley.edu/~charleyc/"}
	     },
	HomePage => "http://www.math.uiuc.edu/Macaulay2/",
    	Headline => "computations of characteristic classes for varieties without equations"
    	)

export { "AbstractSheaf", "abstractSheaf", "AbstractVariety", "abstractVariety", "schubertCycle", "schubertCycle'", "ReturnType",
     "AbstractVarietyMap", "adams", "Base", "BundleRanks", "Bundles", "VarietyDimension", "Bundle",
     "TautologicalLineBundle", "ch", "chern", "ChernCharacter", "ChernClass", "ChernClassVariable", "ctop", "FlagBundle",
     "flagBundle", "projectiveBundle", "projectiveBundle'", "projectiveSpace", "projectiveSpace'", "PP", "PP'", "integral", "IntersectionRing",
     "intersectionRing", "PullBack", "PushForward", "Rank", "ChernClassVariableTable",
     "schur", "SectionClass", "sectionClass", "segre", "StructureMap", "TangentBundle", "tangentBundle", "cotangentBundle", "todd",
     "sectionZeroLocus", "degeneracyLocus", "degeneracyLocus2", "kernelBundle","Pullback",
     "VariableNames", "VariableName", "SubBundles", "QuotientBundles", "point", "base", 
     "toSchubertBasis", "Correspondence", "IncidenceCorrespondence", "intermediates",
     "incidenceCorrespondence","schubertring","intersectionmap","multiFlag",
     "tautologicalLineBundle", "bundles"}

-- not exported, for now: "logg", "expp", "reciprocal", "ToddClass"

protect ChernCharacter
protect ChernClass
protect IntersectionRing
protect TangentBundle
protect ToddClass
protect SourceToTarget
protect TargetToSource
protect Intermediate
protect IntermediateToSource
protect IntermediateToTarget
protect htoschubert
protect schuberttoh
protect schubertring
protect intersectionmap

fixvar = s -> if instance(s,String) then getSymbol s else s

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"
indexSymbols = value Core#"private dictionary"#"indexSymbols"

AbstractVariety = new Type of MutableHashTable
AbstractVariety.synonym = "abstract variety"
globalAssignment AbstractVariety
toString AbstractVariety := net AbstractVariety := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "a variety")
AbstractVariety#{Standard,AfterPrint} = X -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "an abstract variety of dimension " << X.dim << endl;
     )

intersectionRing = method(TypicalValue => Ring)
intersectionRing AbstractVariety := X -> X.IntersectionRing

FlagBundle = new Type of AbstractVariety
FlagBundle.synonym = "abstract flag bundle"
net FlagBundle := toString FlagBundle := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "a flag bundle")
FlagBundle#{Standard,AfterPrint} = X -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "a flag bundle with ranks " << X.BundleRanks << endl;
     )

AbstractVarietyMap = new Type of MutableHashTable
AbstractVarietyMap.synonym = "abstract variety map"
AbstractVarietyMap ^* := Function => f -> f.PullBack
AbstractVarietyMap _* := Function => f -> f.PushForward
globalAssignment AbstractVarietyMap
source AbstractVarietyMap := AbstractVariety => f -> f.source
target AbstractVarietyMap := AbstractVariety => f -> f.target
dim AbstractVarietyMap := f -> dim source f - dim target f
toString AbstractVarietyMap := net AbstractVarietyMap := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "a variety map")
AbstractVarietyMap#{Standard,AfterPrint} = f -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "a map to " << target f << " from " << source f << endl;
     )
AbstractVarietyMap * AbstractVarietyMap := AbstractVarietyMap => (f,g) -> new AbstractVarietyMap from {
     symbol source => source g,
     symbol target => target f,
     PullBack => g.PullBack @@ f.PullBack,
     PushForward => f.PushForward @@ g.PushForward,	    -- may not be efficient
     if g.?SectionClass and f.?SectionClass then SectionClass => g.SectionClass * g.PullBack f.SectionClass
     }

map(FlagBundle,AbstractVarietyMap,List) := AbstractVarietyMap => x -> notImplemented()
map(FlagBundle,AbstractVariety,List) := AbstractVarietyMap => x -> notImplemented()
AbstractVariety#id = (X) -> new AbstractVarietyMap from {
     symbol source => X,
     symbol target => X,
     Pullback => id_(intersectionRing X),
     PushForward => identity,
     SectionClass => 1_(intersectionRing X)
     }
AbstractVariety / AbstractVariety := AbstractVarietyMap => (X,S) -> (
     maps := while X =!= S and X.?StructureMap list (f := X.StructureMap; X = target f; f);
     if #maps == 0 then id_X
     else fold(maps,(f,g) -> g * f))

sectionClass = method(TypicalValue => RingElement)
sectionClass AbstractVarietyMap := f -> f.SectionClass

Correspondence = new Type of MutableHashTable
IncidenceCorrespondence = new Type of Correspondence
IncidenceCorrespondence.synonym = "incidence correspondence"
--SimpleCorrespondence = new Type of Correspondence
--SimpleCorrespondence.synonym = "simple correspondence"
globalAssignment Correspondence
toString Correspondence := net Correspondence := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "a correspondence")
Correspondence#{Standard,AfterPrint} = X -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "a correspondence from " << X.source << " to " << X.target << endl;
     )
toString IncidenceCorrespondence := net IncidenceCorrespondence := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "an incidence correspondence")
IncidenceCorrespondence#{Standard,AfterPrint} = X -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "an incidence correspondence from " << X.source << " to " << X.target << endl;
     )

Correspondence _* := Function => c -> c.SourceToTarget
Correspondence ^* := Function => c -> c.TargetToSource
source Correspondence := AbstractVariety => c -> c.source
target Correspondence := AbstractVariety => c -> c.target
transpose Correspondence := Correspondence => c -> (
     new Correspondence from {
	  global source => target c,
	  global target => source c,
	  SourceToTarget => c.TargetToSource,
	  TargetToSource => c.SourceToTarget})
transpose IncidenceCorrespondence := IncidenceCorrespondence => c -> (
     new IncidenceCorrespondence from {
	  global source => target c,
	  global target => source c,
	  SourceToTarget => c.TargetToSource,
	  TargetToSource => c.SourceToTarget,
	  Intermediate => c.Intermediate,
	  IntermediateToSource => c.IntermediateToTarget,
	  IntermediateToTarget => c.IntermediateToSource})
intermediates = method()
intermediates IncidenceCorrespondence := AbstractVariety => c -> (
     c.Intermediate, c.IntermediateToSource, c.IntermediateToTarget)
Correspondence * Correspondence := Correspondence => (X,Y) -> (
     new Correspondence from {
	  global source => source Y,
	  global target => target X,
	  SourceToTarget => X.SourceToTarget @@ Y.SourceToTarget,
	  TargetToSource => Y.TargetToSource @@ X.TargetToSource})

AbstractSheaf = new Type of HashTable
AbstractSheaf.synonym = "abstract sheaf"
baseName AbstractSheaf := F -> if F.cache.?Name then F.cache.Name else error "unnamed abstract sheaf"
globalAssignment AbstractSheaf
net AbstractSheaf := toString AbstractSheaf := X -> (
     if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
     else "a sheaf")
AbstractSheaf#{Standard,AfterPrint} = E -> (
     << endl;				  -- double space
     << concatenate(interpreterDepth:"o") << lineNumber << " : "
     << "an abstract sheaf of rank " << rank E << " on " << variety E << endl;
     )

abstractSheaf = method(
     TypicalValue => AbstractSheaf,
     Options => {
	  Name => null,
	  ChernClass => null,
	  ChernCharacter => null,
	  Rank => null,
	  })
abstractSheaf AbstractVariety := opts -> X -> (
     local ch; local rk;
     A := intersectionRing X;
     if opts.ChernCharacter =!= null then (
	  ch = opts.ChernCharacter;
	  ch = promote(ch,A);
	  rk = part(0,opts.ChernCharacter);
	  )
     else if opts.Rank =!= null then (
	  ch = rk = promote(opts.Rank,A);
	  --precomputing the Chern character is greatly slowing down some computations
	  if opts.ChernClass =!= null then ch = ch + logg promote(opts.ChernClass,A);
	  )
     else error "expected Rank or ChernCharacter option";
     try rk = lift(rk,ZZ) else try rk = lift(rk,QQ);
     new AbstractSheaf from {
     	  global AbstractVariety => X,
	  ChernCharacter => ch,
	  global cache => new CacheTable from {
	       if opts.Name =!= null then Name => opts.Name,
     	       global rank => rk,
	       if opts.ChernClass =!= null then ChernClass => promote(opts.ChernClass,A)
	       }
     	  }
     )
abstractSheaf(AbstractVariety,ZZ) := 
abstractSheaf(AbstractVariety,QQ) := 
abstractSheaf(AbstractVariety,RingElement) := opts -> (X,f) -> abstractSheaf(X, ChernCharacter => f)

bydegree := net -> f -> (
     if f == 0 then return "0";
     (i,j) := weightRange(first \ degrees (ring f).FlatMonoid, f);
     tms := toList apply(i .. j, n -> part_n f);
     tms = select(tms, p -> p != 0);
     if #tms == 1 then return net expression first tms;
     tms = apply(tms, expression);
     tms = apply(tms, e -> if instance(e,Sum) then new Parenthesize from {e} else e);
     net new Sum from tms)

abstractVariety = method(TypicalValue => AbstractVariety, Options => { ReturnType => AbstractVariety })
abstractVariety(ZZ,Ring) := opts -> (d,A) -> (
     if A.?VarietyDimension then error "ring already in use as an intersection ring";
     if ultimate(coefficientRing,A) =!= QQ then error "expected a QQ-algebra";
     if degreeLength A != 1 then error "expected a ring with degree length 1";
     A.VarietyDimension = d;
     net A := bydegree net;
     toString A := bydegree toString;
     if not ancestor(AbstractVariety,opts#ReturnType) then error "expected value of ReturnType option to be a type of AbstractVariety";
     integral A := (
	  if d === 0
	  then x -> part(d,x)
	  else x -> (hold integral) part(d,x)
	  );	  
     A.Variety = new opts#ReturnType from { global dim => d, IntersectionRing => A })

tangentBundle = method(TypicalValue => AbstractSheaf)
cotangentBundle = method(TypicalValue => AbstractSheaf)
tangentBundle AbstractVariety := X -> (
     if not X.?TangentBundle then error "variety has no tangent bundle";
     X.TangentBundle)
cotangentBundle AbstractVariety := X -> dual tangentBundle X
tangentBundle AbstractVarietyMap := f -> (
     if not f.?TangentBundle 
     then tangentBundle source f - f^* tangentBundle target f
     else f.TangentBundle)
cotangentBundle AbstractVarietyMap := f -> dual tangentBundle f

euler AbstractVariety := X -> integral ctop tangentBundle X

AbstractSheaf QQ := AbstractSheaf ZZ := AbstractSheaf => (F,n) -> (
     if n == 0 then return F;
     X := variety F;
     O1 := tautologicalLineBundle X;
     F **((O1)^**n)
     )
AbstractSheaf RingElement := AbstractSheaf => (F,n) -> (
     if n == 0 then return F;
     X := variety F;
     A := intersectionRing X;
     try n = promote(n,A);
     if not instance(n,A) then error "expected an element in the intersection ring of the variety";
     if not isHomogeneous n then error "expected homogeneous element of degree 0 or 1";
     d := first degree n;
     if d == 0 then (
     	  O1 := tautologicalLineBundle X; 
	  F ** ((O1)^**n)
	  )
     else if d == 1 then (
	  F ** abstractSheaf(X, Rank => 1, ChernClass => 1 + n)
	  )
     else error "expected element of degree 0 or 1"
     )     

integral = method(TypicalValue => RingElement)

protect Bundle
protect args
base = method(Dispatch => Thing, TypicalValue => AbstractVariety)
base Thing := s -> base (1:s)
base Sequence := args -> (
     -- up to one integer, specifying the dimension d of the base
     -- some symbols or indexed variables, to be used as parameter variables of degree 0
     -- some options Bundle => (B,n,b), where B is a symbol or an indexed variable, b is a symbol, and n is an integer, 
     --    specifying that we should provide a bundle named B of rank n whose Chern classes are b_1,...,b_n,
     --    but if n > d then it goes b_1,...,b_d
     degs := vrs := ();
     bdls := {};
     newvr  := (x,d) -> (vrs = (vrs,x);degs = (degs,d));
     newbdl := x -> bdls = append(bdls,x);
     d := null;
     oops := x -> error ("base: unrecognizable argument ",toString x);
     goodvar := x -> try baseName x else error ("unusable as variable: ",toString x);
     goodsym := x -> (
	  s := try baseName x else x;
	  if not instance(s,Symbol) then error ("unusable as subscripted symbol: ",toString x);
	  s);
     scan(args, x -> (
	       if instance(x,Symbol) or instance(x,IndexedVariable) then newvr(x,0)
	       else if instance(x,RingElement) then newvr(baseName x,0)
	       else if instance(x,Option) and #x==2 and x#0 === Bundle and instance(x#1,Sequence) and #x#1== 3 then (
		    (B,n,b) := x#1;
		    if not instance(n,ZZ) then oops x;
     		    if d === null then d = 0;
		    nd := min(n,d);
		    if instance(b,VisibleList) then (
			 if length b != nd then error("expected ",toString nd," variables for the Chern classes of ",toString B);
			 b = apply(toSequence b, goodvar);
			 )
		    else if instance(b,String) then (
			 b = apply(1..nd,i->getSymbol(b|toString i));
			 )
		    else (
		    	 b = goodsym b;
			 b = apply(1..nd,i->b_i);
			 );
		    vrs = (vrs,b);
		    degs = (degs,1..nd);
		    B = goodvar B;
		    newbdl (B,n,b);
		    )
	       else if instance(x,ZZ) then (
		    if #bdls > 0 then error "integer argument (the dimension) should be first";
		    if d =!= null then error "more than one integer argument encountered (as the dimension)";
		    d = x)
	       else oops x));
     if d === null then d = 0;
     vrs = deepSplice vrs;
     degs = toList deepSplice degs;
     A := QQ[vrs,Degrees => degs, DegreeRank => 1];
     X := abstractVariety(d,A);
     X.TangentBundle = abstractSheaf(X,Rank => d);          -- it's the base; user can replace it
     X.TautologicalLineBundle = abstractSheaf(X,Rank => 1); -- it's the base; user can replace it
     integral intersectionRing X := (
	  if d === 0
	  then x -> part(d,x)
	  else x -> (hold integral) part(d,x)
	  );
     X#"bundles" = apply(bdls,(B,n,b) -> (
	       globalReleaseFunction(B,value B);
	       B <- abstractSheaf(X, Name => B, Rank => n, ChernClass => 1_A + sum(1 .. min(n,d), i -> A_(b#(i-1))));
	       globalAssignFunction(B,value B);
	       (B,value B)));
     X.args = args;
     X)
point = base()
integral intersectionRing point := r -> if liftable(r,ZZ) then lift(r,ZZ) else lift(r,QQ)

dim AbstractVariety := X -> X.dim
chern = method(TypicalValue => RingElement)
chern AbstractSheaf := (cacheValue ChernClass) (F -> expp F.ChernCharacter)
chern(ZZ, AbstractSheaf) := (p,F) -> part(p,chern F)
chern(ZZ, ZZ, AbstractSheaf) := List => (p,q,F) -> toList apply(p..q, i -> chern(i,F))

ctop = method(TypicalValue => RingElement)
ctop AbstractSheaf := F -> chern_(rank F) F

ch = method(TypicalValue => RingElement)
ch AbstractSheaf := (F) -> F.ChernCharacter
ch(ZZ,AbstractSheaf) := (n,F) -> part_n ch F

protect symbol$
ChernClassVariableTable = new Type of MutableHashTable
net ChernClassVariableTable := Etable -> net Etable # symbol$
baseName ChernClassVariableTable := Etable -> Etable # symbol$
ChernClassVariable = new Type of BasicList
ChernClassVariable.synonym = "Chern class variable"
getCCVTable = E -> (
     Etable := value E;
     if not instance(Etable,ChernClassVariableTable) then (
	  if E =!= Etable then stderr << "--warning: clearing value of symbol " << E << " to allow access to Chern class variables based on it" << endl;
	  E <- Etable = new ChernClassVariableTable;
	  Etable#symbol$ = E;
	  );
     Etable)
chern(ZZ,Symbol) := ChernClassVariable => (n,E) -> ( getCCVTable E; new ChernClassVariable from {n,E} )
chern(ZZ,ChernClassVariableTable) := (n,E) -> if E#?n then E#n else new ChernClassVariable from {n,E#symbol$}
Ring _ ChernClassVariable := (R,s) -> R#indexSymbols#s
baseName ChernClassVariable := identity
installMethod(symbol <-, ChernClassVariable, (c,x) -> (getCCVTable c#1)#(c#0) = x)
value ChernClassVariable := c -> ( n := c#0; E := c#1; Etable := value E; if instance(Etable,ChernClassVariableTable) then Etable#n else c)
expression ChernClassVariable := c -> new FunctionApplication from {new Subscript from {symbol c,c#0}, c#1}
net ChernClassVariable := net @@ expression
toString ChernClassVariable := toString @@ expression
ChernClassVariable .. ChernClassVariable := (a,b) -> (
     if a#1 =!= b#1 then error "expected Chern class variables based on the same symbol";
     apply(a#0 .. b#0, i -> new ChernClassVariable from {i,a#1} ))

installMethod(symbol _, OO, RingElement, AbstractSheaf => (OO,D) -> (
	  if D != 0 and degree D != {1} then error "expected a cycle class of degree 1 (a divisor class)";
	  1 - OO_(variety D)(-D)))
installMethod(symbol _, OO, AbstractVariety, AbstractSheaf => 
     (OO,X) -> (
	  A := intersectionRing X;
	  abstractSheaf(X, Rank => 1, ChernCharacter => 1_A, ChernClass => 1_A))
     )

AbstractSheaf * RingElement := 
AbstractSheaf * QQ := (E,n) -> n*E
RingElement * AbstractSheaf := (n,E) -> (
     if degree n =!= {0} then error "expected a ring element of degree 0";
     abstractSheaf(variety E, ChernCharacter => n * ch E))
QQ * AbstractSheaf := AbstractSheaf => (n,E) -> abstractSheaf(variety E, ChernCharacter => n * ch E)

ZZ * AbstractSheaf := AbstractSheaf => (n,E) -> E^n
AbstractSheaf * ZZ := 
AbstractSheaf ^ ZZ := AbstractSheaf => (E,n) -> new AbstractSheaf from {
     global AbstractVariety => E.AbstractVariety,
     ChernCharacter => n * E.ChernCharacter,
     symbol cache => new CacheTable from {
     	  global rank => E.cache.rank * n,
	  if E.cache.?ChernClass and n >= 0 then ChernClass => E.cache.ChernClass ^ n
	  }
     }

geometricSeries = (t,n,dim) -> (			    -- computes (1+t)^n assuming t^(dim+1) == 0
     ti := 1;
     bin := 1;
     r := 1;
     for i from 1 to dim do (
	  bin = (1/i) * (n-(i-1)) * bin;
	  ti = ti * t;
	  r = r + bin * ti);
     r)

AbstractSheaf ^** ZZ := AbstractSheaf => (E,n) -> (
     if n == 1 then return E;
     if n < 0 then (
	  if rank E =!= 1 then error "negative tensor power of sheaf of rank not equal to 1 requested";
	  E = dual E;
	  n = - n;
	  );
     abstractSheaf(variety E, ChernCharacter => part(0,dim variety E,(ch E)^n)))

AbstractSheaf ^** QQ := AbstractSheaf ^** RingElement := AbstractSheaf => (E,n) -> (
     if rank E != 1 then error "non-integer tensor power of sheaf of rank not equal to 1 requested";
     abstractSheaf(variety E, Rank => 1, ChernCharacter => geometricSeries(ch E - 1, n, dim variety E)))

rank AbstractSheaf := RingElement => E -> E.cache.rank
variety AbstractSheaf := AbstractVariety => E -> E.AbstractVariety
variety Ring := AbstractVariety => R -> R.Variety
variety RingElement := AbstractVariety => r -> variety ring r

tangentBundle FlagBundle := (stashValue TangentBundle) (FV -> tangentBundle FV.Base + tangentBundle FV.StructureMap)

assignable = v -> instance(v,Symbol) or null =!= lookup(symbol <-, class v)

offset := 1
flagBundle = method(Options => { VariableNames => null }, TypicalValue => FlagBundle)
flagBundle(List) := opts -> (bundleRanks) -> flagBundle(bundleRanks,point,opts)
flagBundle(List,AbstractVariety) := opts -> (bundleRanks,X) -> flagBundle(bundleRanks,OO_X^(sum bundleRanks),opts)
flagBundle(List,AbstractSheaf) := opts -> (bundleRanks,E) -> (
     h$ := getSymbol "H";
     varNames := opts.VariableNames;
     bundleRanks = splice bundleRanks;
     if not all(bundleRanks,r -> instance(r,ZZ) and r>=0) then error "expected bundle ranks to be non-negative integers";
     n := #bundleRanks;
     rk := sum bundleRanks;
     hft := {1};
     HR := degreesRing hft;
     T := HR_0;
     vn := dualpart(0,rsort bundleRanks);
     hilbertSeriesHint := new Divide from {
	  promote( product for i from 0 to n-1 list ( k := sum take(bundleRanks,i); product for j from k+1 to k+bundleRanks#i list 1 - T^j ), HR),
	  new Product from reverse for i from 1 to #vn list new Power from {1 - T^i, vn#(i-1)}
	  };
     if rank E != rk then error "expected rank of bundle to equal sum of bundle ranks";
     if part(rk+1,infinity,chern E) != 0 then error "expected an effective bundle (vanishing higher Chern classes)";
     verror := () -> error "flagBundle VariableNames option: expected a good name or list of names";
     varNames = (
	  if varNames === null then varNames = h$;
	  varNames = fixvar varNames;
	  if instance(varNames,Symbol)
	  then apply(0 .. #bundleRanks - 1, bundleRanks, (i,r) -> apply(toList(1 .. r), j -> new IndexedVariable from {varNames,(i+offset,j)}))
	  else if instance(varNames,List)
	  then (
	       if #varNames != n then error("expected ", toString n, " bundle names");
	       apply(0 .. #bundleRanks - 1, bundleRanks, (i,r) -> (
		    h := varNames#i;
		    try h = baseName h;
		    if h === null then apply(toList(1 .. r), j -> new IndexedVariable from {h$,(i+offset,j)})
		    else if instance(h,Symbol) then apply(toList(1 .. r), j -> new IndexedVariable from {h,j})
		    else if instance(h,String) then apply(toList(1 .. r), j -> getSymbol(h|toString j))
		    else if instance(h,List) then (
			 h = splice h;
			 if #h != r then error("flagBundle: expected variable name sublist of length ",toString r);
			 apply(h, v -> (
				   try v = baseName v;
				   if not assignable v then error "flagBundle: encountered unusable name in variable list";
				   v)))
		    else verror())))
     	  else verror());
     -- done with user-interface preparation and checking
     Ord := GRevLex;
     X := variety E;
     dgs := splice apply(bundleRanks, r -> 1 .. r);
     S := intersectionRing X;
     U := S(monoid [flatten varNames, Degrees => dgs, MonomialOrder => apply(bundleRanks, n -> Ord => n), Join => false, Heft => hft, DegreeRank => 1]);
     -- (A,F) := flattenRing U; G := F^-1 ;
     A := U; F := identity;
     chclasses := apply(varNames, x -> F (1_U + sum(x,v -> U_v)));
     rlns := product chclasses - F promote(chern E,U);
     rlns = sum @@ last \ sort pairs partition(degree,terms(QQ,rlns));
     rlns = ideal matrix(U,{rlns});
     if heft S =!= null and degreesRing S === HR then gb(rlns, Hilbert => numerator hilbertSeriesHint * numerator hilbertSeries S);
     B := A/rlns;
     -- (C,H) := flattenRing B; I := H^-1;
     C := B; H := identity;
     -- use C;
     C#"hilbert Function hint" = hilbertSeriesHint;
     d := dim X + sum(n, i -> sum(i+1 .. n-1, j -> bundleRanks#i * bundleRanks#j));
     FV := C.Variety = abstractVariety(d,C,ReturnType => FlagBundle);
     FV.BundleRanks = bundleRanks;
     FV.Rank = rk;
     FV.Base = X;
     bundles := FV.Bundles = apply(0 .. n-1, i -> (
	       bdl := abstractSheaf(FV, Rank => bundleRanks#i, ChernClass => H promote(chclasses#i,B));
	       bdl));
     FV.SubBundles = (() -> ( t := OO_FV^0; for i from 0 to n list if i == 0 then t else t = t + bundles#(i-1)))();
     FV.QuotientBundles = (() -> ( t := OO_FV^0; for i from 0 to n list if i == 0 then t else t = t + bundles#(n-i)))();
     --next line is taking a long time to run because computation of Chern character is slow
     --FV.TautologicalLineBundle = OO_FV(sum(1 .. #bundles - 1, i -> i * chern(1,bundles#i)));
     pullback := method();
     pushforward := method();
     pullback ZZ := pullback QQ := r -> promote(r,C);
     pullback S := r -> H promote(F promote(r,U), B);
     sec := if n === 0 then 1_C else product(1 .. n-1, i -> (ctop bundles#i)^(sum(i, j -> rank bundles#j)));
     pushforward C := r -> coefficient(sec,r);
     pullback AbstractSheaf := E -> (
	  if variety E =!= X then "pullback: variety mismatch";
	  abstractSheaf(FV,Rank => rank E, ChernClass => pullback chern E));
     p := new AbstractVarietyMap from {
	  global target => X,
	  global source => FV,
	  SectionClass => sec,
	  PushForward => pushforward,
	  PullBack => pullback
	  };
     FV.StructureMap = p;
     pushforward AbstractSheaf := E -> (
	  if variety E =!= FV then "pushforward: variety mismatch";
	  abstractSheaf(X,ChernCharacter => pushforward (ch E * todd p)));
     integral C := r -> integral p_* r;
     FV.StructureMap.TangentBundle = (
	  if #bundles > 0
	  then sum(1 .. #bundles-1, i -> sum(i, j -> Hom(bundles#j,bundles#i)))
	  else OO_FV^0);
     if X.?TangentBundle then FV.TangentBundle = FV.StructureMap.TangentBundle + FV.StructureMap^* X.TangentBundle;
     use FV;
     FV)

use AbstractVariety := AbstractVariety => X -> (
     use intersectionRing X;
     if X#?"bundles" then scan(X#"bundles",(sym,shf) -> sym <- shf);
     X)

installMethod(symbol SPACE, OO, RingElement, AbstractSheaf => (OO,h) -> OO_(variety ring h) (h))

projectiveBundle = method(Options => { VariableNames => null }, TypicalValue => FlagBundle)
projectiveBundle ZZ := opts -> n -> flagBundle({n,1},opts)
projectiveBundle(ZZ,AbstractVariety) := opts -> (n,X) -> flagBundle({n,1},X,opts)
projectiveBundle AbstractSheaf := opts -> E -> flagBundle({rank E - 1, 1},E,opts)

projectiveBundle' = method(Options => { VariableNames => null }, TypicalValue => FlagBundle)
projectiveBundle' ZZ := opts -> n -> flagBundle({1,n},opts)
projectiveBundle'(ZZ,AbstractVariety) := opts -> (n,X) -> flagBundle({1,n},X,opts)
projectiveBundle' AbstractSheaf := opts -> E -> flagBundle({1, rank E - 1},E,opts)

projectiveSpace = method(Options => { VariableName => "h" }, TypicalValue => FlagBundle)
projectiveSpace ZZ := opts -> n -> flagBundle({n,1},VariableNames => {,{fixvar opts.VariableName}})
projectiveSpace(ZZ,AbstractVariety) := opts -> (n,X) -> flagBundle({n,1},X,VariableNames => {,{fixvar opts.VariableName}})

projectiveSpace' = method(Options => { VariableName => "h" }, TypicalValue => FlagBundle)
projectiveSpace' ZZ := opts -> n -> flagBundle({1,n},VariableNames => {{fixvar opts.VariableName},})
projectiveSpace'(ZZ,AbstractVariety) := opts -> (n,X) -> flagBundle({1,n},X,VariableNames => {{fixvar opts.VariableName},})

PP  = new ScriptedFunctor from { superscript => i -> projectiveSpace i }
PP' = new ScriptedFunctor from { superscript => i -> projectiveSpace' i }

bundles = method()
bundles FlagBundle := X -> X.Bundles
tautologicalLineBundle = method()
tautologicalLineBundle AbstractVariety := X -> (
     if X.?TautologicalLineBundle then X.TautologicalLineBundle else
     error "variety does not have a tautological line bundle")
tautologicalLineBundle FlagBundle := X -> (
     if X.?TautologicalLineBundle then X.TautologicalLineBundle else (
	  B := bundles X;
	  X.TautologicalLineBundle = OO_X(sum(1 .. #B - 1, i -> i * chern(1,B#i)));
	  X.TautologicalLineBundle))

--given L a basepoint-free line bundle on an AbstractVariety X over some other variety B,
--and P the projectivization of a bundle E on B, mapstope(X,P,L) builds the map
--from X to P such that the pullback of O_P(1) is L.  Note that while specifying such a map
--requires a surjection from (the pullback of E to X) onto L, the intersection theory does
--not depend on the choice of surjection
--
--warning: Schubert2 does not check that the line bundle provided is basepoint-free
--
--warning 2: default is Fulton notation, currently no way to access Grothendieck-style if
--target projective space has dimension 1
map(FlagBundle,AbstractVariety,AbstractSheaf) := opts -> (P,X,L) -> (
     --by Charley Crissman
     B := P.Base;
     try f := X / B else error "expected first variety to have same base as projective bundle";
     if not #P.Bundles == 2 then error "expected a projective bundle";
     if not (P.BundleRanks#0 == 1 or P.BundleRanks#1 == 1) then error "expected a projective bundle";
     if not (rank L == 1) then error "expected a line bundle";
     fulton := (P.BundleRanks#0 == 1); --Fulton-style notation?
     RB := intersectionRing B;
     RX := intersectionRing X;
     RP := intersectionRing P;
     (S,Q) := P.Bundles;
     n := P.Rank - 1;
     p := P.StructureMap;
     cE := lift(chern(S + Q),RB);
     E := abstractSheaf(B, Rank => n+1, ChernClass=>cE);
     sE := if fulton then reciprocal chern E else reciprocal chern dual E;
     H := if fulton then -chern(1,S) else chern(1,Q);
     cL := chern(1,L);
     local aclasses;
     local nextclass;
     pfmap := a -> (
	 aclasses = {}; --eventual pushforward of a will be sum_{i=0}^n a_i*H^(n-i)
	 for i from 0 to n do (
	      nextclass = sum for j from 0 to i-1 list (
	           aclasses#j * part(i-j,sE));
	      nextclass = f_*(a*((cL)^i)) - nextclass;
	      aclasses = append(aclasses,nextclass));
	 sum for i from 0 to n list (H^(n-i))*(p^*(aclasses#i)));
     pushforward := method();
     pushforward RX := a -> pfmap a;
     M := if fulton then (matrix {{-cL} | for i from 1 to n list (
          chern(i, (f^* E) + L))})
     else (matrix {(for i from 1 to n list (
	  chern(i, (f^* E) - L))) | {cL}});
     pbmap := map(RX,RP,M);
     pullback := method();
     pullback RP := a -> pbmap a;
     pullback AbstractSheaf := F -> (
	  if variety F =!= P then error "pullback: variety mismatch";
	  abstractSheaf(X,Rank => rank F,ChernClass => pullback chern F));
     ourmap := new AbstractVarietyMap from {
          global target => P,
          global source => X,
          PushForward => pushforward,
          PullBack => pullback};
     if X.?TangentBundle then (--can't build pushforward of sheaves without relative tangent bundle
          pushforward AbstractSheaf := F -> (
   	  if variety F =!= X then error "pushforward: variety mismatch";
	       abstractSheaf(P,ChernCharacter => pushforward (ch F * todd ourmap))))
     --can we compute relative tangent bundle to this map without tangent bundle of X?
     else pushforward AbstractSheaf := F -> (
          error "cannot push forward sheaves along map with no relative tangent bundle");
     ourmap)
 
--Given a base variety X, bundles E_1,..,E_n on X, and a list of lists of integers
--L = {{a_(1,1),..,a_(1,k_1)}, ... , {a_(n,1),..,a_(n,k_n)}},
--let F_1 = flagBundle({a_(1,1),..,a_(1,k_1)},E_1), let p_1 be the structure map from F1 to X,
--and recursively let F_i = flagBundle({a_(i,1),..,a_(i,k_i)},p_(i-1)^* E_i)
--and p_i be the composition of p_(i-1) and the structure map of F_(i-1).
--then multiFlag(L,{E_1,..,E_n}) is F_n, but is constructed in a single step
--rather than iteratively.
--
--Equivalently, this is the fiber product over X of the varieties
--flagBundle({a_(i,1),..,a_(i,k_i)}) for all i.
--
--This method is not exported and not meant to be user accessed; it is used in building forgetful
--maps of flag varieties.
multiFlag = method()
multiFlag(List,List) := (bundleRanks, bundles) -> (
     --by Charley Crissman
     K := local K;
     if not #bundleRanks == #bundles then error "expected same number of bundles as lists of ranks";
     if not all(bundleRanks, l -> all(l, r -> instance(r,ZZ) and r>=0)) then error "expected bundles ranks to be positive integers";
     X := variety bundles#0;
     if not all(bundles, b -> (variety b) === X) then error "expected all bundles over same base";
     n := #bundleRanks;
     for i from 0 to n-1 do (
	  if not sum(bundleRanks#i) == rank bundles#i then error "expected rank of bundle to equal sum of bundle ranks");
     varNames := apply(0 .. n-1, i -> apply(1 .. #(bundleRanks#i), bundleRanks#i, (j,r) ->(
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
     MF := C.Variety = abstractVariety(d,C);
     MF.Base = X;
     MF.Bundles = apply(0 .. n-1, l -> (
	         	       apply(0 .. #(bundleRanks#l)-1, i -> (
			 bdl := abstractSheaf(MF, Rank => bundleRanks#l#i, ChernClass => H promote(chclasses#l#i,B));
			 bdl))));
     pullback := method();
     pushforward := method();
     pullback ZZ := pullback QQ := r -> promote(r,C);
     pullback S := r -> promote(r, B);
     --pullback S := r -> promote(promote(r,U), B);
     --probably take out the if n == 0 part
     sec := if n === 0 then 1_C else (
	  product(0 .. n-1, l-> (
		    if #(bundleRanks#l) === 0 then 1_C else (
		         product(1 .. #(bundleRanks#l)-1, i -> promote((ctop MF.Bundles#l#i)^(sum(i, j -> bundleRanks#l#j)),B))))));
     pushforward C := r -> coefficient(sec,r);
     pullback AbstractSheaf := E -> (
	  if variety E =!= X then error "pullback-variety mismatch";
	  abstractSheaf(MF,Rank => rank E, ChernClass => pullback chern E));
     p := new AbstractVarietyMap from {
	  global target => X,
	  global source => MF,
	  SectionClass => sec,
	  PushForward => pushforward,
	  PullBack => pullback
	  };
     MF.StructureMap = p;
     tangentBundles := toList apply(MF.Bundles, L -> (
	  if #L > 1
	  then sum(1..#L-1, i -> sum(i,j -> Hom(L#j,L#i)))
	  else OO_MF^0));
     MF.StructureMap.TangentBundle = sum tangentBundles;
     pushforward AbstractSheaf := E -> (
	  if variety E =!= MF then error "pushforward: variety mismatch";
	  abstractSheaf(X,ChernCharacter => pushforward(ch E * todd p)));
     integral C := r -> integral p_* r;
     --computing the tangent bundle of MF is very slow and likely unnecessary
     --if X.?TangentBundle then MF.TangentBundle = MF.StructureMap.TangentBundle + p^* X.TangentBundle;
     MF
     )

--map(X,Y) is the "forgetful map" from Y to X
--this method depends heavily on knowing the generators and monomial order of the
--intersection ring of a flag variety and will break if those are ever changed
map(FlagBundle,FlagBundle) := opts -> (B,A) -> (
     --by Charley Crissman
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
     (RMF',k1) := flattenRing(RMF,CoefficientRing=>RB);
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

incidenceCorrespondence = method(TypicalValue => IncidenceCorrespondence)
incidenceCorrespondence(List) := L -> (
     if not #L == 3 then error "expected a list of length 3";
     if not all(L, i-> instance(i,ZZ) and i > 0) then "expected a list of positive integers";
     if not L#0 < L#2 and L#1 < L#2 then "expected last list element to be largest";
     G1 := flagBundle({L#0,L#2 - L#0});
     G2 := flagBundle({L#1,L#2 - L#1});
     incidenceCorrespondence(G2,G1))
incidenceCorrespondence(List,AbstractSheaf) := (L,B) -> (
     if not #L == 2 then error "expected a list of length 2";
     if not all(L, i-> instance(i,ZZ) and i > 0) then "expected a list of positive integers";
     n := rank B;
     if not all(L, i-> n > i) then "expected a list of integers smaller than rank of bundle";
     G1 := flagBundle({L#0,n - L#0},B);
     G2 := flagBundle({L#1,n - L#1},B);
     incidenceCorrespondence(G2,G1))
--is more efficient than using two forgetful maps because it creates one less intermediate object
--currently only accepts Grassmannians but could be easily extended now that we have forgetful maps of flag varieties
incidenceCorrespondence(FlagBundle,FlagBundle) := (G2,G1) -> (
     --by Charley Crissman
     if G1.Base =!= G2.Base then error "expected FlagBundles over same base";
     B := intersectionRing G1.Base;
     if not (#G1.Bundles == 2 and #G2.Bundles == 2) then error "expected two Grassmannians";
     n := sum G1.BundleRanks;
     if not n == (sum G2.BundleRanks) then error "expected Grassmannians of same bundle";
     (s1,q1) := G1.Bundles;
     (s2,q2) := G2.Bundles;
     a := rank s1;
     b := rank s2;
     if a > b then transpose incidenceCorrespondence(G1,G2) else (
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
	      global source => G1,
	      global target => G2,
	      Intermediate => I1,
	      IntermediateToSource => f,
	      IntermediateToTarget => g * iso,
	      SourceToTarget => sourcetotarget,
	      TargetToSource => targettosource};
	 rez))

reciprocal = method(TypicalValue => RingElement)
reciprocal RingElement := (A) -> (
     -- computes 1/A (mod degree >=(d+1))
     -- ASSUMPTION: part(0,A) == 1.
     d := (ring A).VarietyDimension;
     a := for i from 0 to d list part_i(A);
     recip := new MutableList from splice{d+1:0};
     recip#0 = 1_(ring A);
     for n from 1 to d do
       recip#n = - sum(1..n, i -> a#i * recip#(n-i));
     sum toList recip
     )

logg = method(TypicalValue => RingElement)
logg QQ := logg ZZ := (n) -> 0
logg RingElement := (C) -> (
     -- C is the total chern class in an intersection ring A
     -- The chern character of C is returned.
     A := ring C;
     d := A.VarietyDimension;
     p := new MutableList from splice{d+1:0}; -- p#i is (-1)^i * (i-th power sum of chern roots)
     e := for i from 0 to d list part(i,C); -- elem symm functions in the chern roots
     for n from 1 to d do
         p#n = -n*e#n - sum for j from 1 to n-1 list e#j * p#(n-j);
     promote(sum for i from 1 to d list 1/i! * (-1)^i * p#i, A))

expp = method(TypicalValue => RingElement)
expp QQ := expp ZZ := (n) -> 1
expp RingElement := (y) -> (
     -- y is the chern character
     -- the total chern class of y is returned
     A := ring y;
     d := A.VarietyDimension;
     p := for i from 0 to d list (-1)^i * i! * part(i,y);
     e := new MutableList from splice{d+1:0};
     e#0 = 1_A;
     for n from 1 to d do
	  e#n = - 1/n * sum for j from 1 to n list p#j * e#(n-j);
     sum toList e
     )

todd = method(TypicalValue => RingElement)
todd AbstractSheaf := E -> todd' ch E
todd AbstractVariety := X -> todd tangentBundle X
todd AbstractVarietyMap := p -> todd tangentBundle p
todd' = (r) -> (
     -- r is the chern character
     -- the (total) todd class is returned
     A := ring r;
     if not A.?VarietyDimension then error "expected a ring with its variety dimension set";
     if r == 0 then return 1_A;
     d := A.VarietyDimension;
     -- step 1: find the first part of the Taylor series for t/(1-exp(-t))
     denom := for i from 0 to d list (-1)^i /(i+1)!;
     invdenom := new MutableList from splice{d+1:0};
     invdenom#0 = 1;
     for n from 1 to d do 
       invdenom#n = - sum for i from 1 to n list denom#i * invdenom#(n-i);
     -- step 2.  logg.  This is more complicated than desired.
     R := QQ (monoid[getSymbol "t"]);
     R.VarietyDimension = d;
     td := logg sum for i from 0 to d list invdenom#i * R_0^i;
     td = for i from 0 to d list coefficient(R_0^i,td);
     -- step 3.  exp
     expp sum for i from 0 to d list i! * td#i * part(i,r))

--chi = method(TypicalValue => RingElement)
chi AbstractSheaf := F -> integral(todd variety F * ch F)

segre = method(TypicalValue => RingElement)
segre AbstractSheaf := E -> reciprocal chern dual E
segre(ZZ, AbstractSheaf) := (p,F) -> part(p,segre F)
-- we don't need this one:
-- segre(ZZ, ZZ, AbstractSheaf) := (p,q,F) -> (s := segre F; toList apply(p..q, i -> part(i,s)))

nonnull := x -> select(x, i -> i =!= null)

coerce := (F,G) -> (
     X := variety F;
     Y := variety G;
     if X === Y then return (F,G);
     AX := intersectionRing X;
     AY := intersectionRing Y;
     z := try 0_AX + 0_AY else error "expected abstract sheaves on compatible or equal varieties";
     if ring z === AX
     then (F, abstractSheaf(X,Rank => rank G, ChernClass => chern G)   )
     else (   abstractSheaf(Y,Rank => rank F, ChernClass => chern F), G)
     )

AbstractSheaf ++ RingElement := 
AbstractSheaf + RingElement := AbstractSheaf => (F,n) -> (
     if degree n =!= {0} then error "expected a ring element of degree 0";
     abstractSheaf(variety F, ChernCharacter => ch F + n))
AbstractSheaf ++ QQ := 
AbstractSheaf + QQ := 
AbstractSheaf ++ ZZ := 
AbstractSheaf + ZZ := AbstractSheaf => (F,n) -> abstractSheaf(variety F, ChernCharacter => ch F + n)
RingElement + AbstractSheaf := 
RingElement ++ AbstractSheaf := AbstractSheaf => (n,F) -> (
     if degree n =!= {0} then error "expected a ring element of degree 0";
     abstractSheaf(variety F, ChernCharacter => n + ch F))
QQ ++ AbstractSheaf := 
QQ + AbstractSheaf := 
ZZ ++ AbstractSheaf := 
ZZ + AbstractSheaf := AbstractSheaf => (n,F) -> abstractSheaf(variety F, ChernCharacter => n + ch F)

AbstractSheaf ++ AbstractSheaf :=
AbstractSheaf + AbstractSheaf := AbstractSheaf => (
     (F,G) -> abstractSheaf nonnull (
	  variety F, Rank => rank F + rank G,
	  ChernCharacter => ch F + ch G,
	  if F.cache.?ChernClass and G.cache.?ChernClass then 
	    ChernClass => F.cache.ChernClass * G.cache.ChernClass
	  )) @@ coerce

adams = method()
adams(ZZ,RingElement) := RingElement => (k,ch) -> (
     d := first degree ch;
     sum(0 .. d, i -> k^i * part_i ch))
adams(ZZ,AbstractSheaf) := AbstractSheaf => (k,E) -> abstractSheaf nonnull (variety E, Rank => rank E, 
     ChernCharacter => adams(k, ch E),
     if E.cache.?ChernClass then ChernClass => adams(k, E.cache.ChernClass)
     )
dual AbstractSheaf := AbstractSheaf => {} >> o -> E -> adams(-1,E)

- AbstractSheaf := AbstractSheaf => E -> abstractSheaf(variety E, Rank => - rank E, ChernCharacter => - ch E)
AbstractSheaf - AbstractSheaf := AbstractSheaf => ((F,G) -> F + -G) @@ coerce
AbstractSheaf - RingElement := AbstractSheaf => (F,n) -> (
     if degree n =!= {0} then error "expected a ring element of degree 0";
     abstractSheaf(variety F, ChernCharacter => ch F - n))
AbstractSheaf - QQ := 
AbstractSheaf - ZZ := AbstractSheaf => (F,n) -> abstractSheaf(variety F, ChernCharacter => ch F - n)
RingElement - AbstractSheaf := AbstractSheaf => (n,F) -> (
     if degree n =!= {0} then error "expected a ring element of degree 0";
     abstractSheaf(variety F, ChernCharacter => n - ch F))
QQ - AbstractSheaf := 
ZZ - AbstractSheaf := AbstractSheaf => (n,F) -> abstractSheaf(variety F, ChernCharacter => n - ch F)

AbstractSheaf ** AbstractSheaf :=
AbstractSheaf * AbstractSheaf := AbstractSheaf => (
     (F,G) -> (
	  f := ch F;
	  g := ch G;
	  X := variety F;
	  if f == 1 then G
	  else if g == 1 then F
	  else abstractSheaf(X, ChernCharacter => part(0,dim X,f*g)))
     ) @@ coerce

Hom(AbstractSheaf, AbstractSheaf) := AbstractSheaf => (F,G) -> dual F ** G

det AbstractSheaf := AbstractSheaf => opts -> (F) -> abstractSheaf(variety F, Rank => 1, ChernClass => 1 + part(1,ch F))

computeWedges = (n,A,d) -> (
     -- compute the chern characters of wedge(i,A), for i = 0..n, given a chern character, truncating above degree d
     wedge := new MutableList from splice{0..n};
     wedge#0 = 1_(ring A);
     wedge#1 = A;
     for p from 2 to n do
	  wedge#p = 1/p * sum for m from 0 to p-1 list (-1)^(p-m+1) * part(0,d,wedge#m * adams(p-m,A));
     toList wedge
     )

exteriorPower(ZZ, AbstractSheaf) := AbstractSheaf => opts -> (n,E) -> (
     -- wedge is an array 0..n of the chern characters of the exerior 
     -- powers of E.  The last one is what we want.

     -- this line of code is incorrect for virtual bundles:
     -- if 2*n > rank E then return det(E) ** dual exteriorPower(rank E - n, E);

     wedge := computeWedges(n,ch E,dim variety E);
     abstractSheaf(variety E, ChernCharacter => wedge#n)
     )

exteriorPower AbstractSheaf := AbstractSheaf => opts -> (E) -> (
     -- really only makes sense if E is "effective", but it's useful, anyway
     sum for i from 0 to rank E list (-1)^i * exteriorPower(i,E)
     )

symmetricPower(RingElement, AbstractSheaf) := AbstractSheaf => (n,F) -> (
     X := variety F;
     A := intersectionRing X;
     try n = promote(n,A);
     if not instance(n,A) then error "expected an element in the intersection ring of the variety";
     if not isHomogeneous n or degree n =!= {0} then error "expected homogeneous element of degree 0";
     -- This uses Grothendieck-Riemann-Roch, together with the fact that
     -- f_!(OO_PF(n)) = f_*(symm(n,F)), since the higher direct images are 0.
     h := local h;
     PF := projectiveBundle(F, VariableNames => h);
     f := PF.StructureMap;
     abstractSheaf(X, f_*(part(0,dim PF,ch OO_PF(n) * todd f))))

symmetricPower(ZZ, AbstractSheaf) := 
symmetricPower(QQ, AbstractSheaf) := AbstractSheaf => (n,E) -> (
     d := dim variety E;
     A := ch E;
     wedge := computeWedges(n,A,d);
     symms := new MutableList from splice{0..n};
     symms#0 = 1_(ring A);
     symms#1 = A;
     for p from 2 to n do (
	  r := min(p, rank E);
	  symms#p = sum for m from 1 to r list (-1)^(m+1) * part(0,d,wedge#m * symms#(p-m));
	  );
     abstractSheaf(variety E, ChernCharacter => symms#n)
     )

schur = method(TypicalValue => AbstractSheaf)
schur(List, AbstractSheaf) := (p,E) -> (
     -- Make sure that p is a monotone descending sequence of non-negative integers
     --q := conjugate new Partition from p;
     p = splice p;
     q := p;
     n := sum p;
     R := symmRing n;
     wedges := computeWedges(n,ch E,dim variety E);
     J := jacobiTrudi(q,R); -- so the result will be a poly in the wedge powers
     F := map(ring ch E, R, join(apply(splice{0..n-1}, i -> R_i => wedges#(i+1)), 
	                         apply(splice{n..2*n-1}, i -> R_i => 0)));
     abstractSheaf(variety E, ChernCharacter => F J))

schubertCycle = method(TypicalValue => RingElement)
schubertCycle' = method(TypicalValue => RingElement)
FlagBundle _ Sequence := FlagBundle _ List := RingElement => (F,s) -> schubertCycle(s,F)
giambelli =  (r,E,b) -> (
     p := matrix for i from 0 to r-1 list for j from 0 to r-1 list chern(b#i-i+j,E); -- Giambelli's formula, also called Jacobi-Trudi
     if debugLevel > 15 then stderr << "giambelli : " << p << endl;
     det p
     )
listtoseq = (r,b) -> toSequence apply(#b, i -> r + i - b#i)
seqtolist = (r,b) ->            apply(#b, i -> r + i - b#i)
dualpart  = (r,b) -> splice for i from 0 to #b list ((if i === #b then r else b#(-i-1)) - (if i === 0 then 0 else b#-i)) : #b - i

schubertCycle(Sequence,FlagBundle) := (a,X) -> (
     if #X.BundleRanks != 2 then error "expected a Grassmannian";
     n := X.Rank;
     E := dual first X.Bundles;
     s := rank E;
     q := n-s;
     if q != #a then error("expected a sequence of length ", toString q);
     for i from 0 to q-1 do (
	  ai := a#i;
	  if not instance(ai,ZZ) or ai < 0 then error "expected a sequence of non-negative integers";
	  if i>0 and not (a#(i-1) < a#i) then error "expected a strictly increasing sequence of integers";
	  if not (ai < n) then error("expected a sequence of integers less than ",toString n);
	  );
     giambelli(q,E,seqtolist(s,a)))
schubertCycle(List,FlagBundle) := (b,X) -> (
     -- see page 271 of Fulton's Intersection Theory for this notation
     if #X.BundleRanks != 2 then error "expected a Grassmannian";
     E := dual first bundles X;
     s := rank E;
     n := X.Rank;
     q := n-s;
     if q != #b then error("expected a list of length ", toString q);
     for i from 0 to q-1 do (
	  bi := b#i;
	  if not instance(bi,ZZ) or bi < 0 then error "expected a list of non-negative integers";
	  if i>0 and not (b#(i-1) >= b#i) then error "expected a decreasing list of integers";
	  if not (bi <= s) then error("expected a list of integers bounded by ",toString(s));
	  );
     giambelli(q,E,b))
schubertCycle'(Sequence,FlagBundle) := (a,X) -> (
     if #X.BundleRanks != 2 then error "expected a Grassmannian";
     n := X.Rank;
     E := last X.Bundles;
     q := rank E;
     s := n-q;
     if s != #a then error("expected a sequence of length ", toString s);
     for i from 0 to s-1 do (
	  ai := a#i;
	  if not instance(ai,ZZ) or ai < 0 then error "expected a sequence of non-negative integers";
	  if i>0 and not (a#(i-1) < a#i) then error "expected a strictly increasing sequence of integers";
	  if (ai < n) then error("expected a sequence of integers less than", toString n);
	  );
     giambelli(s,E,seqtolist(q,a)))
schubertCycle'(List,FlagBundle) := (b,X) -> (
     -- see page 271 of Fulton's Intersection Theory for this notation
     if #X.BundleRanks != 2 then error "expected a Grassmannian";
     E := last X.Bundles;
     q := rank E;
     n := X.Rank;
     s := n-q;
     if s != #b then error("expected a list of length ", toString s);
     for i from 0 to s-1 do (
	  bi := b#i;
	  if not instance(bi,ZZ) or bi < 0 then error "expected a list of non-negative integers";
	  if i>0 and not (b#(i-1) >= b#i) then error "expected a decreasing list of integers";
	  if not (bi <= q) then error("expected a list of integers bounded by ",toString(q));
	  );
     giambelli(s,E,b))

diagrams = method()
diagrams(ZZ,ZZ) := (k,n) -> ( --diagrams {k>=a_1>=...>=a_n>=0}
     if n==1 then apply(k+1, i->{i})
     else flatten apply(k+1, i -> apply(diagrams(i,n-1), l -> flatten {i,l})))     
diagrams(ZZ,ZZ,ZZ) := (k,n,d) -> (--partitions of d of above form
     select(diagrams(k,n), i -> (sum(i) == d)))

toSchubertBasis = method()
toSchubertBasis(RingElement) := c -> (
     --by Charley Crissman
     try G := variety c else error "expected an element of an intersection ring"; 
     if not (instance(G,FlagBundle) and #G.BundleRanks == 2) then error "expected a Grassmannian";
     R := intersectionRing G;
     B := intersectionRing (G.Base);
     (k,q) := toSequence(G.BundleRanks);
     P := diagrams(q,k);
     M := apply(P, i-> schubertCycle'(i,G));
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
	  S.cache.intersectionmap = map(R,S,M);
     	  S * S := (f,g) -> (
	       f1 := S.cache.intersectionmap(f);
	       g1 := S.cache.intersectionmap(g);
	       toSchubertBasis(f1*g1)
	       );
	  S ^ ZZ := (f,n) -> (
	       f2 := S.cache.intersectionmap(f);
	       toSchubertBasis((f2)^n));
	  R.cache.schubertring = S
	  );
     rez := (vars S)*(lift(c2,B));
     rez_(0,0)
     )


sectionZeroLocus = method(TypicalValue => AbstractVariety)
sectionZeroLocus AbstractSheaf := (F) -> (
     -- adapted from Schubert's bundlesection
     X := variety F;
     A := intersectionRing X;
     classZ := ctop F;
     B := A[Join=>false];		      -- a way to get a copy of A
     Z := abstractVariety(dim X - rank F, B);
     pullback := method();
     pullback ZZ := pullback QQ := pullback A := r -> promote(r,B);
     pullback AbstractSheaf := E -> (
	  if variety E =!= X then "pullback: variety mismatch";
	  abstractSheaf(Z, Rank => rank E, ChernClass => pullback chern E));
     pushforward := method();
     pushforward ZZ := pushforward QQ := r -> pushforward promote(r,B);
     pushforward B := b -> lift(b,A) * classZ;
     i := Z.StructureMap = new AbstractVarietyMap from {
     	  symbol source => Z,
     	  symbol target => X,
     	  PullBack => pullback,
     	  PushForward => pushforward,
	  TangentBundle => abstractSheaf(Z, ChernCharacter => - ch F)
	  };
     pushforward AbstractSheaf := E -> abstractSheaf(X,ChernCharacter => pushforward (ch E * todd i));
     integral B := m -> integral( lift(m,A) * classZ );
     if X.?TangentBundle then Z.TangentBundle = abstractSheaf(Z, ChernCharacter => ch tangentBundle X - ch F);
     Z)

degeneracyLocus2 = method(TypicalValue => RingElement)
degeneracyLocus2(ZZ,AbstractSheaf,AbstractSheaf) := (k,B,A) -> (
     X := variety B;
     if X =!= variety A then error "expected sheaves on the same variety";
     m := rank A;
     n := rank B;
     part( (m-k)*(n-k), ch schur( { n - k : m - k }, B - A )))

degeneracyLocus = method(TypicalValue => AbstractVariety)
degeneracyLocus(ZZ,AbstractSheaf,AbstractSheaf) := (k,B,A) -> (
     X := variety B;
     if X =!= variety A then error "expected sheaves on the same variety";
     m := rank A;
     n := rank B;
     G := flagBundle({m-k,k},A);
     S := first G.Bundles;
     sectionZeroLocus Hom(S,(G/X)^* B))

kernelBundle = method(TypicalValue => AbstractVariety)
kernelBundle(ZZ,AbstractSheaf,AbstractSheaf) := (k,B,A) -> (
     X := variety A;
     Z := degeneracyLocus(k,B,A);
     G := target Z.StructureMap;
     S := first G.Bundles;
     K := (Z/G)^* S;
     Z.StructureMap = Z/X;
     K)

beginDocumentation()
multidoc get (currentFileDirectory | "Schubert2/doc.m2")
undocumented {
     (tangentBundle,FlagBundle),
     (symmetricPower,QQ,AbstractSheaf),
     (symmetricPower,ZZ,AbstractSheaf),
     (net,ChernClassVariableTable),
     (net,AbstractSheaf),
     (net,AbstractVariety),
     (net,AbstractVarietyMap),
     (net,ChernClassVariable),
     (net,FlagBundle),
     (net,Correspondence),
     (net,IncidenceCorrespondence),
     (baseName,ChernClassVariable),
     (expression,ChernClassVariable),
     (baseName,AbstractSheaf),
     (baseName,ChernClassVariableTable),
     (toString,AbstractSheaf),
     (toString,AbstractVariety),
     (toString,AbstractVarietyMap),
     (toString,ChernClassVariable),
     (toString,FlagBundle),
     (toString,Correspondence),
     (toString,IncidenceCorrespondence)
     }
load (Schubert2#"source directory"|"Schubert2/test-charley.m2")
TEST /// input (Schubert2#"source directory"|"Schubert2/demo.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/demo2.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/demo3.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/test-dan.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/test2-dan.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/blowup-test.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/BrillNoether-test.m2") ///
TEST /// input (Schubert2#"source directory"|"Schubert2/SymmetricProduct-test.m2") ///

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/packages PACKAGES=Schubert2 all check-Schubert2 RemakeAllDocumentation=true RerunExamples=true RemakePackages=true"
-- End:
