restart
--Discuss Flag bundles, notation, specializing to G(k,n), P^n
--Example 1: Schubert cycles on GG(1,3)
loadPackage "Schubert2"
G = flagBundle({2,2},VariableNames => {s,q})
(S,Q) = G.Bundles
intersectionRing G
ideal gens gb ideal oo
--Briefly discuss Chern classes
sigma_1 = schubertCycle'({1,0},G) --note the '
toSchubertBasis sigma_1
toSchubertBasis ((sigma_1)^2)
oo^2

--Example 2: The Plucker embedding
restart
loadPackage "Schubert2"
G = flagBundle({2,2},VariableNames => {s,q})
AG = intersectionRing G
(S,Q) = G.Bundles
L = exteriorPower(2,dual S)
P5 = flagBundle({5,1},VariableNames => {,h})
AP5 = intersectionRing P5
H = chern(1,last P5.Bundles) --the hyperplane class on P5
f = map(P5,G,L)
toSchubertBasis f^* H --a hyperplane section of GG13 in the Plucker embedding
f_* (1_AG) --pushforward of the fundamental class of GG13, conclude degree = 2

--Example 3: Lines meeting four general curves of degree d
restart
loadPackage "Schubert2"
S = base d --S2 can use base parameters to stand for variables in formulas
G = flagBundle({2,2},S,VariableNames => {s,q})
--can build the class of lines meeting a general curve of degree d in one of two ways:
--(1): book formula
sigma_1 = schubertCycle'({1,0},G)
curveclass = d*sigma_1
numoflines = integral (curveclass^4)
sub(numoflines,d=>3) -- num of lines meeting 4 general cubics
--(2): incidence correspondence
P3 = flagBundle({1,3},S,VariableNames => {h,b})
I = incidenceCorrespondence(G,P3)
H = chern(1,last P3.Bundles) --the hyperplane class on P3
C = d*(H^2)
toSchubertBasis I^* C --class of lines meeting C

--Example 4: Secants to two general twisted cubics
--For each d and g we build the cycle in GG13 of lines secant
--to a general curve of degree d and genus g:  
restart
loadPackage "Schubert2"
S = base(g,d)
G = flagBundle({2,2},S,VariableNames => {s,q})
sigma_2 = schubertCycle'({2,0},G)
sigma_(1,1) = schubertCycle'({1,1},G)
--now can use book formula to write down the class in GG13 of the locus of chords of a general
--curve of degree d and genus g
cycleofchords = ((d-1)*(d-2)/2 - g)*sigma_2 + (d*(d-1)/2)*sigma_(1,1)
toSchubertBasis cycleofchords
--we square and take the degree to get the number of common chords
--to two general curves of deg d, genus g
numofchords = integral cycleofchords^2
sub(numofchords,{d=>3,g=>0/1})

--Example 5: Lines meeting 6 general 2-planes in P4
restart
loadPackage "Schubert2"
G = flagBundle({2,3})
sigma_1 = schubertCycle'({1,0},G) --lines meeting a 2-plane
integral ((sigma_1)^6)

--Afterword: IntersectionTheory.m2
loadPackage "IntersectionTheory"
viewHelp IntersectionTheory