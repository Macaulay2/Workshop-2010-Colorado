--sub does not work properly with base rings in Schubert2:

restart
needsPackage "Schubert2"
S = base(d,g)
intersectionRing S --base ring looks like a poly ring in g and d
c2 = (1/2)*d^4 - 2*(d^3) - d^2*g + (7/2)*d^2 + 3*d*g + g^2 - 3*d - 2*g + 1
sub(c2,{d=>3,g=>0}) --sub gives back 82
(3^4)/2 - 2*(3^3) + (7/2)*(3^2) - 3*3 + 1 --the actual value is 10
