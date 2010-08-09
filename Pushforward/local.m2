--A primitive version of the local computation package in Macaulay2
--provided by Mike Stillman.

setMaxIdeal = method()
setMaxIdeal(Ideal) := (maxI) -> (
     R := ring maxI;
     R.residueMap = map(R,R,vars R % maxI);
     R.maxIdeal = maxI
     )

localComplement = method()
localComplement Matrix := Matrix => (m) -> (
     n := transpose syz transpose ((ring m).residueMap m);
     id_(target n) // n)

defaultResolutionLength := (R) -> (
     numgens R + 1 + if ZZ === ultimate(coefficientRing, R) then 1 else 0
     )

resolutionLength := (R,options) -> (
     if options.LengthLimit == infinity then defaultResolutionLength R else
options.LengthLimit
     )

localsyz = method()
localsyz(Matrix) := (m) -> (
     C = res(coker m,LengthLimit=>3);
     C.dd_2 * localComplement(C.dd_3))

localMingens = method()
localMingens(Matrix) := Matrix => (m) -> (
     -- warning: this routine should perhaps take a Module...
     m * localComplement syz m
     )

localModulo = method()
localModulo(Matrix,Matrix) := Matrix => (m,n) -> (
     P := target m;
     Q := target n;
     if P != Q then error "expected maps with the same target";
     if not isFreeModule P or not isFreeModule Q
     or not isFreeModule source m or not isFreeModule source n
     then error "expected maps between free modules";
     localMingens syz(m|n, SyzygyRows => numgens source m)
     )


localPrune = method()
localPrune Module := (M) -> (
     p = presentation M;
     p1 = localComplement p;
     p2 = localModulo(p1,p);
     N := coker(p2);
     N.cache.pruningMap = map(M,N,p1);
     N
     )

localResolution = method(Options => options resolution)
localResolution Module := options -> (M) -> (
     R := ring M;
     maxlength := resolutionLength(R,options);
     if M.cache.?resolution
     then (C := M.cache.resolution;
     C.length = length C)
     else (
	  C = new ChainComplex;
	  C.ring = R;
	  f := presentation M;
	  C#0 = target f;
	  C#1 = source f;
	  C.dd#1 = f;
	  M.cache.resolution = C;
	  C.length = 1;
	  );
     i := C.length;
     while i < maxlength and C.dd#i != 0 do (
	  g := localsyz C.dd#i;
	  shield (
	       i = i+1;
	       C.dd#i = g;
	       C#i = source g;
	       C.length = i;
	       );
	  );
     C)

end




