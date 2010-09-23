needsPackage "Schubert2"


--given L a line bundle on an AbstractVariety X over some other variety B,
--and P the projectivization of a bundle E on B, mapstope(X,P,L) builds the map
--from X to P such that the pullback of O_P(1) is L.  Note that while specifying such a map
--requires a surjection from (the pullback of E to X) onto L, the intersection theory does
--not depend on the choice of surjection

map(FlagBundle,AbstractVariety,AbstractSheaf) := opts -> (P,X,L) -> (
     B := P.Base;
     try f := X / B else error "expected first variety to have same base as projective bundle";
     if not (#P.Bundles == 2 and P.BundleRanks#0 == 1) then error "currently supports only maps to Fulton-style P^n";
     if not (rank L == 1) then error "expected a line bundle";
     RB := intersectionRing B;
     RX := intersectionRing X;
     RP := intersectionRing P;
     (S,Q) := P.Bundles;
     n := P.Rank - 1;
     p := P.StructureMap;
     cE := lift(chern(S + Q),RB);
     E := abstractSheaf(B, Rank => n+1, ChernClass=>cE);
     sE := chern dual E;
     H := -chern(1,S);
     cL := chern(1,L);
     pfmap := a -> (
	  local aclasses;
	  local nextclass;
	  aclasses = {}; --eventual pushforward of a will be sum_{i=0}^n a_i*H^(n-i)
	  for i from 0 to n do (
	       nextclass = sum for j from 0 to i-1 list (
		    aclasses#j * part(i-j,sE));
	       nextclass = f_*(a*((cL)^i)) - nextclass;
	       aclasses = append(aclasses,nextclass));
	  sum for i from 0 to n list (H^(n-i))*(p^*(aclasses#i)));
     pushforward := method();
     pushforward RX := a -> pfmap a;
     M := matrix {{-cL} | for i from 1 to n list (
	  chern(i, (f^* E) + L))};
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
     else pushforward AbstractSheaf := F -> (
	  error "cannot push forward sheaves along map with no relative tangent bundle");
     ourmap
     )

end
---
restart
load "mapstope.m2"

--example 1: plucker embedding of GG(1,3)
X = flagBundle({2,2})
(S,Q) = X.Bundles
L = exteriorPower(2,dual S)
P = flagBundle({1,5})
f = map(P,X,L) -- Plucker embedding of GG(1,3) in PP^5
H = P.Bundles#0
f^* (chern(1,H)) -- neg hyperplane section, should be -sigma_1
f_* chern(0,S) --expect 2 times hyperplane class since GG(1,3) has degree 2

--example 2: plucker embedding of GG(1,4)
X = flagBundle({2,3})
(S,Q) = X.Bundles
L = exteriorPower(2,dual S)
P = flagBundle({1,9})
f = map(P,X,L)
H = P.Bundles#0
f^* (chern(1,H)) -- neg hyperplane section, should be -sigma_1
f_* chern(0,S) --should give degree of GG(1,4) (i.e. 5) times cube of hyperplane class
f_* S
chern oo
