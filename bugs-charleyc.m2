--sub does not work properly with base rings in Schubert2:
--"resolved" in the sense that this bug was tracked down to a terrible design decision with sub:
--it turns out that substituting integers into a polynomial with rational coefficients will
--somehow coerce the polynomial into a polynomial ring over ZZ before substituting

restart
needsPackage "Schubert2"
S = base(d,g)
intersectionRing S --base ring looks like a poly ring in g and d
c2 = (1/2)*d^4 - 2*(d^3) - d^2*g + (7/2)*d^2 + 3*d*g + g^2 - 3*d - 2*g + 1
sub(c2,{d=>3,g=>0}) --sub gives back 82
(3^4)/2 - 2*(3^3) + (7/2)*(3^2) - 3*3 + 1 --the actual value is 10

--A simple example of this ugly decision:
restart
S = QQ[x]
p = (1/2)*x
sub(p,{x=>2})
