
signAndShuffle := (a,b) -> (
     ct := 0;
     i := 0; m := #a;
     j := 0; n := #b;
     sh := while a#?i or b#?j list (
	  t := if a#?i then a#i;
	  u := if b#?j then b#j;
     	  if t === u then return (0,);
	  if t === null then (j = j+1; u)
	  else if u === null or t < u then (i = i+1; t)
     	  else (ct = ct + m-i; j = j+1; u));
     ((-1)^ct, toSequence sh));

signOfShuffle := (a,b) -> (
     ct := 0;
     i := 0; m := #a;
     j := 0; n := #b;
     while i<m and j<n do (
     	  if a#i == b#j then return 0;
     	  if a#i < b#j then i = i+1
     	  else (ct = ct + m-i; j = j+1));
     (-1)^ct);
     
Grassmannian(ZZ,ZZ):= o -> (k,n) -> Schubert(k,n,n-k..n,o)
Grassmannian(ZZ,ZZ,PolynomialRing) := o -> (k,n,R) -> (
     I := Grassmannian(k,n,o);
     S := ring I;
     if numgens R < numgens S then error ("expected a ring with at least ",toString numgens S," generators");
     f := map(R,S,apply(numgens S, i -> R_i));
     f I)

Schubert(ZZ, ZZ, VisibleList) := o -> (k,n,sigma) -> (
     time (
     L := toSequence \ subsets(n+1,k+1);
     R := o.CoefficientRing (monoid [apply(L, i -> new IndexedVariable from {baseName o.Variable,unsequence i})]);
     vr := new HashTable from apply(#L, i -> L#i => R_i);
     higher := apply( select( L, s -> any(s, sigma, (a,b) -> a>b)), s -> vr#s );
     G := flatten for i from 0 to #L-1 list for j from i+1 to #L-1 list (
	  r := L#i;
	  s := L#j;
	  up := position(r, s, (a,b) -> a>b);
	  if up === null then continue;
	  snake := s_{0..up} | r_{up..k};
	  sum for s1 in subsets(snake,up+1) list (
	       s2 := snake - set s1;
	       (sgn1,c) := signAndShuffle(r_{0..up-1}, s2);
	       if sgn1 == 0 then continue;
	       (sgn2,d) := signAndShuffle(s1, s_{up+1..k});
	       if sgn2 == 0 then continue;
	       sgn := sgn1 * sgn2 * signOfShuffle(s1,s2);
	       sgn * vr#c * vr#d));
     );
     time g := generators forceGB matrix(R,{(G|higher)});
     time forceGB g;
     ideal g)

end

restart
load "schubert-test.m2"
Grassmannian(3,6, CoefficientRing=>ZZ/101);
Grassmannian(4,8, CoefficientRing=>ZZ/101);
time Grassmannian(4,9, CoefficientRing=>ZZ/101);
time Grassmannian(4,9, CoefficientRing=>QQ);
time Grassmannian(4,10, CoefficientRing=>ZZ/101);

