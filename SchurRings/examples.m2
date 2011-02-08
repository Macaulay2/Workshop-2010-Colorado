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
time toS plE;
time toS(plE,Strategy=>Stillman)--this is also slow


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
