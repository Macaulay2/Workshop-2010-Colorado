----------
--Tests for toSchubertBasis
----------


TEST ///
--Test 1 for toSchubertBasis: GG(1,3) = G(2,4)
G = flagBundle({2,2})
(S,Q) = bundles G
R = intersectionRing G
sigma_1 = schubertCycle({1,0},G)
if sigma_1 != chern(1,Q) then error "something's wrong with schubertCycle"
--list the Schubert cycles in the order used by S
L = flatten for i from 0 to 2 list (
     for j from 0 to i list (toSchubertBasis schubertCycle({i,j},G)))
S = first schubertRing G
--next line is checking that the basis of S is the Schubert basis of R
assert (flatten entries vars S == L)
s = toSchubertBasis sigma_1
--next line checks that multiplication in the Schubert ring is working correctly
assert (toSchubertBasis((sigma_1)^2) == s^2)
///

TEST ///
--Test 2 for toSchubertBasis: multiplication in G(3,6)
G = flagBundle({3,3})
c1 = schubertCycle({2,1,0},G) --(c1)^2 = s_{2,2,2} + 2s_{3,2,1} + s_{3,3,0}
c2 = schubertCycle({3,2,1},G)
a = coefficient(toSchubertBasis(c2),toSchubertBasis((c1)^2))
assert (a == 2)
///

TEST ///
--Test 3 for toSchubertBasis
P = flagBundle({4,1})
B = first bundles P
h = chern(1,last bundles P)
G = flagBundle({2,2},B)
(S,T,U) = schubertRing G
gens S
c1 = schubertCycle({1,0},G)
c2 = schubertCycle({2,0},G)
s1 = toSchubertBasis c1
s2 = toSchubertBasis c2
assert(s1 == (gens S)#1)
assert(s2 == (gens S)#3) --note that this will fail if generator order is changed
gens S
assert(toSchubertBasis (c1^2) == (s1^2))
assert(s1*s2 == (gens S)#4)
s1^3
--next formula was verified by hand
assert((toSchubertBasis(-h^3-h^2*c1-h*(c1^2-c2)+2*c1*c2)) == s1^3)
///

----------
--Tests for incidenceCorrespondence(FlagBundle,FlagBundle)
----------
TEST ///
--Test 1 for incidenceCorrespondence(FlagBundle,FlagBundle)
P = flagBundle({1,3})
G = flagBundle({2,2})
RP = intersectionRing P
RG = intersectionRing G
I = incidenceCorrespondence(G,P)
assert(source I === P)
assert(target I === G)
h = chern(1,last bundles P) --the hyperplane class
s1 = chern(1,last bundles G) --sigma_1
s2 = chern(2,last bundles G) --sigma_2
--checking pushforward and pullback on bases of both rings:
assert(I_* 1_RP == 0_RG)
assert(I_* h == 1_RG)
assert(I_* (h^2) == s1)
assert(I_* (h^3) == s2)
assert(I^* 1_RG == 0_RP)
assert(I^* s1 == 0_RP)
assert(I^* s2 == 1_RP)
assert(I^* (s1^2 - s2) == 0_RP) --sigma_1,1
assert(I^* (s1*s2) == h)
assert(I^* s2^2 == h^2)
///

TEST ///
--Test 2 for incidenceCorrespondence(FlagBundle,FlagBundle)
--Comparing results for incidenceCorrespondence and forgetful maps
X = flagBundle({4,5})
Y = flagBundle({2,7})
Z = flagBundle({2,2,5})--should be the intermediate variety of the inc cor
I = incidenceCorrespondence(Y,X)
f = map(X,Z)
g = map(Y,Z)
RX = intersectionRing X
RY = intersectionRing Y
for x in flatten entries basis RX do (
     assert(I_* x == g_* f^* x))
for y in flatten entries basis RY do (
     assert(I^* y == f_* g^* y))
///

----------
--Tests for map(FlagBundle,FlagBundle)
----------
TEST ///
--Test 1 for map(FlagBundle,FlagBundle)
X = flagBundle({3,3,3})
RX = intersectionRing X
Y = flagBundle({1,2,2,1,3})
f = map(X,Y)
relpt = chern(2,Y.Bundles#1)*((chern(1,Y.Bundles#3))^2) --the relative class of a point
assert(f_* relpt == 1_RX) --pushforward of class of a relative point, should be 1
assert(f^* chern last bundles X == chern last bundles Y)
assert(f_* (relpt * (f^* chern last bundles X)) == (
	  chern last bundles X)) -- f_*(relpt*f^*(a)) = a
assert(f_* (relpt * (f^* chern first bundles X)) == (
	  chern first bundles X)) -- f_*(relpt*f^*(a)) = a
///

TEST ///
--Test 2 for map(FlagBundle,FlagBundle)
G = flagBundle({4,3})
RG = intersectionRing G
(S,Q) = G.Bundles
Y = flagBundle({1,3,3}) --should be same as P(S)
g = map(G,Y)
z = -chern(1,Y.Bundles#0) -- the class of O(1) considering Y as P(S)
assert(g_* (z^3) == 1_RG) --0th segre class of S, should be 1
assert(g_* (z^4) == chern(1,Q))--1st segre class of S (=1st chern class of Q)
assert(g_* (z^5) == chern(2,Q))--2nd segre class of S (=2nd chern class of Q)
assert(g_* (z^6) == chern(3,Q))--etc
--next examples check push-pull for segre class intersections:
assert(g_* (z^3 * (g^* chern(1,S))) == chern(1,S))
assert(g_* (z^5 * (g^* chern(1,S))) == chern(1,S)*chern(2,Q))
///

TEST ///
--Test 3 for map(FlagBundle,FlagBundle): with base parameter
A = base n
G = flagBundle({4,3},A)
(S,Q) = bundles G
Y = flagBundle({1,3,3},A) --should be same as P(S)
g = map(G,Y)
z = -chern(1,first bundles Y)*n -- the class of O(n) considering Y as P(S)
AG = intersectionRing G
assert(g_* (z^3) == n^3*1_AG) --n^3 times 0th segre class of S, should be n^3
assert(g_* (z^4) == n^4*chern(1,Q))--n^4 times 1st segre class of S
assert(g_* (z^5) == n^5*chern(2,Q))--n^5 times 2nd Segre class of S
///

TEST ///
--Test 4 for map(FlagBundle,FlagBundle)
B = flagBundle({8,1})
RB = intersectionRing B
(S,Q) = bundles B
X = flagBundle({4,4},S)
RX = intersectionRing X
(E,E') = bundles X
Y = flagBundle({2,2,2,2},S)
RY = intersectionRing Y
--Y should be isomorphic to flagBundle({2,2},E) times flagBundle({2,2},E') over X
(F,F',F'',F''') = bundles Y
f = map(X,Y)
--checking that bundles on X pull back correctly:
assert(chern(f^* E) == chern(F + F'))
assert(chern(f^* E') == chern(F'' + F'''))
--checking pushforwards of relative points
relptXY = ((chern(2,F'))^2)*((chern(2,F'''))^2)--relative point of Y over X
assert(f_* relptXY == 1_RX)
relptBY = ((chern(2,F'))^2)*((chern(2,F''))^4)*((chern(2,F'''))^6)--rel pt of Y over B
relptBX = (chern(4,E'))^4 --relative point of X over B
assert(f_* relptBY == relptBX)
--checking that "triangle commutes"
g = X/B
h = g*f
h' = Y/B
for b in flatten entries basis RB do (
     assert(h^* b == h'^* b))
basis RY
for b in flatten entries basis RY do (
     assert(h_* b == h'_* b))--takes a long time, RY has a 2520-element basis
///

----------
--Tests for map(FlagBundle,AbstractVariety,AbstractSheaf)
----------
TEST ///
--Test 1 for map(FlagBundle,AbstractVariety,AbstractSheaf):
--the Plucker embedding of GG(1,3) in PP^5
X = flagBundle({2,2})
(S,Q) = X.Bundles
L = exteriorPower(2,dual S)
P = flagBundle({1,5})
f = map(P,X,L) -- Plucker embedding of GG(1,3) in PP^5
H = first bundles P --O(-1)
assert(f^* (chern(1,H)) == -chern(1,Q)) -- neg hyperplane section, should be -sigma_1
assert(f_* chern(0,S) == -2*chern(1,H)) --expect 2 times hyperplane class since GG(1,3) has degree 2
///

TEST ///
--Test 2 for map(FlagBundle,AbstractVariety,AbstractSheaf):
--the Plucker embedding of GG(1,4) in PP^9
X = flagBundle({2,3})
(S,Q) = X.Bundles
L = exteriorPower(2,dual S)
P = flagBundle({1,9})
H = first bundles P
f = map(P,X,L)
assert(f^* (chern(1,H)) == -chern(1,Q)) -- neg hyperplane section, should be -sigma_1
assert(f_* chern(0,S) == -5*((chern(1,H))^3)) --should give degree of GG(1,4) (i.e. 5) times cube of hyperplane class
///

TEST ///
--Test 3 for map(FlagBundle,AbstractVariety,AbstractSheaf):
--same as test 2, but Grothendieck-style:
X = flagBundle({2,3})
(S,Q) = X.Bundles
L = exteriorPower(2,dual S)
P = flagBundle({9,1})
f = map(P,X,L)
H = last bundles P
assert(f^* (chern(1,H)) == chern(1,Q)) -- hyperplane section, should be sigma_1
assert(f_* chern(0,S) == 5*((chern(1,H))^3)) --should give degree of GG(1,4) (i.e. 5) times cube of hyperplane class
///

TEST ///
--Test 4 for map(FlagBundle,AbstractVariety,AbstractSheaf):
--maps from PP^1 x PP^1
P1 = flagBundle({1,1})
O1 = last bundles P1
P1xP1 = flagBundle({1,1},P1)
RP1xP1 = intersectionRing P1xP1
p1 = P1xP1/P1
O10 = p1^*O1
O01 = last bundles P1xP1
p2 = map(P1,P1xP1,O01) --the second projection map
assert(p2^*O1 === O01)
assert(p2_* 1_RP1xP1 == 0)
assert(p2_*(chern(1,O10)*chern(1,O01)) == chern(1,O1))
P3 = flagBundle({1,3})
L = O10**O01
f = map(P3,P1xP1,L) --embedding of P1xP1 as a quadric surface
assert(f_* 1_RP1xP1 == 2*chern(1,last bundles P3)) --should be surface of degree 2
///

----------
--Tests for tautologicalLineBundle
----------

TEST ///
S = base n
X = flagBundle({3,3,4},S)
L = OO_X(1)
chern L
assert(X.TautologicalLineBundle === L)
///