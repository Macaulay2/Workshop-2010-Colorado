restart
loadPackage"SchurRings"

S = schurRing2(QQ,s,5)
T = schurRing2(S,t,4)

f = 1_S*t_{2,1}
g = s_{2,1}*1_T

f-g


restart
loadPackage "SchurRings"



S = schurRing2(QQ,s,3)
S1 = schurRing2(S,t,6)

f = s_{5}*t_{3}
f^3 + f * f * f --this shouldn't be 0
f^3

g = s_{1}*t_{1}
g^3+g*g*g -- this shouldn't be 0

(s_{1}+t_{2})^2 --this isn't right

f = s_{1}+t_{2}
f = t_{2} + s_{1}

restart
loadPackage"SchurRings"
viewHelp "SchurRings"
----creation of EtoH tables etc. are slow
time R = symmRing 30


----toS works faster for the h-polynomials in this case
----they're both slow
time R = symmRing 30
plH = time plethysm(h_5,h_6);
time toS plH;
plE = time plethysm(e_5,e_6);
time toS plE,Strategy=>Stillman);
time toS(plE,Strategy=>Stembridge)--this is also slow (239.93 seconds on my MBP)
  -- used 3.5 GB, result is only 493 monomials...!


-----
time R = symmRing 30
plP = time plethysm(h_5,h_6);--0.26
plH = time toH plP;--2.94
plE = time toE plH;--3.4
time toH plE;--13.72

------
S = schurRing(s,30)
time plethysm(s_{5},s_{6});
time plethysm(s_{4,1},s_{6});
time plethysm(s_{3,1,1},s_{6});
time plethysm(s_{1,1,1,1,1},s_{1,1,1,1,1,1}); --takes a long time, see plethysm(e_5,e_6)


-----determinant is slow
-----
-----second version takes 15s, and the first takes < 1s
R = symmRing 30
time jacobiTrudi({3,3,3,3,3,3,2,2,2,2,2,2},R,Memoize=>true);
time jacobiTrudi({3,3,3,3,3,3,2,2,2,2,2,2},R,Memoize=>false);

-------- maple code here
/Library/Frameworks/Maple.framework/Versions/Current/bin/maple

with(linalg);
with(SF);
f := plethysm(h5,h6);
fh := toh(f);
fe := toe(fh);
fh2 := toh(fe);
fs := tos(fh);
fs2 := tos(fe);
-------------------------

------- Some tests to be added to the main file ----------------------
R = schurRing2(QQ,s)
F = s_{2,1}
F^2 == s_(4,2)+s_(4,1,1)+s_(3,3)+2*s_(3,2,1)+s_(3,1,1,1)+s_(2,2,2)+s_(2,2,1,1)

-- test of dimensions
restart
debug loadPackage "SchurRings"
R = schurRing2(QQ,r,3)
S = schurRing2(R,s,4)
F = r_{2,1}
dim F
dim(4,F)
A = QQ[n]
dim(n,F)
G = r_{2,1} * s_{3}
dim G
A = QQ[m,n]
dim({n,m},G)
value oo
----------------------------------------------------------------------
