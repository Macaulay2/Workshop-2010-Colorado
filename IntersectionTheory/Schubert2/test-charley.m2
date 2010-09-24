----------
--Tests for toSchubertBasis
----------
TEST ///
--Test 1 for toSchubertBasis: GG(1,3) = G(2,4)
G = flagBundle({2,2})
(S,Q) = G.Bundles
R = intersectionRing G
sigma_1 = schubertCycle'({1,0},G)
if sigma_1 != chern(1,Q) then error "something's wrong with schubertCycle'"
--list the Schubert cycles in the order used by S
L = flatten for i from 0 to 2 list (
     for j from 0 to i list (toSchubertBasis schubertCycle'({i,j},G)))
S = R.cache.schubertring
--next line is checking that the basis of S is the Schubert basis of R
assert (flatten entries vars S == L)
s = toSchubertBasis sigma_1
--next line checks that multiplication in the Schubert ring is working correctly
assert (toSchubertBasis((sigma_1)^2) == s^2)
///

TEST ///
--Test 2 for toSchubertBasis: multiplication in G(3,6)
G = flagBundle({3,3})
c1 = schubertCycle'({2,1,0},G) --(c1)^2 = s_{2,2,2} + 2s_{3,2,1} + s_{3,3,0}
c2 = schubertCycle'({3,2,1},G)
a = coefficient(toSchubertBasis(c2),toSchubertBasis((c1)^2))
assert (a == 2)
///

TEST ///
--Should have tests for G(k,E) with E nontrivial, need to compute by hand first
///

----------
--Tests for incidenceCorrespondence(flagBundle,flagBundle)
----------

--Tests for map(flagBundle,flagBundle)

--Tests for map(flagBundle,AbstractVariety,AbstractSheaf)

--Tests for tautologicalLineBundle