-- Computations for Shidoku with Boolean polynomials.  FP are the field polynomials, K1 are the shidoku polynomials and K2 is a set of initial clues to give a unique answer.

restart
S=ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder=>Lex]
--R=ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4]
FP= {a1*(a1-1), a2*(a2-1), a3*(a3-1), a4*(a4-1), b1*(b1-1), b2*(b2-1), b3*(b3-1), b4*(b4-1), c1*(c1-1), c2*(c2-1), c3*(c3-1), c4*(c4-1), d1*(d1-1), d2*(d2-1), d3*(d3-1), d4*(d4-1), e1*(e1-1), e2*(e2-1), e3*(e3-1), e4*(e4-1), f1*(f1-1), f2*(f2-1), f3*(f3-1), f4*(f4-1), g1*(g1-1), g2*(g2-1), g3*(g3-1), g4*(g4-1), h1*(h1-1), h2*(h2-1), h3*(h3-1), h4*(h4-1), i1*(i1-1), i2*(i2-1), i3*(i3-1), i4*(i4-1), j1*(j1-1), j2*(j2-1), j3*(j3-1), j4*(j4-1), k1*(k1-1), k2*(k2-1), k3*(k3-1), k4*(k4-1), l1*(l1-1), l2*(l2-1), l3*(l3-1), l4*(l4-1), m1*(m1-1), m2*(m2-1), m3*(m3-1), m4*(m4-1), n1*(n1-1), n2*(n2-1), n3*(n3-1), n4*(n4-1), q1*(q1-1), q2*(q2-1), q3*(q3-1), q4*(q4-1), p1*(p1-1), p2*(p2-1), p3*(p3-1), p4*(p4-1)}
I=ideal(FP)
--QR=R/FP
K1={a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
K2 ={d1, d2, d3, d4-1, e1, e2, e3, e4-1, g1, g2-1, g3, g4, j1, j2, j3-1, j4, l1-1, l2, l3, l4, m1-1, m2, m3, m4}
K3={f2, f3, f4, g2, g3, j3, k3,d1}
K3={a1, e4, g2, k3, n3, p4, j2, n2, p2, q2}
J=ideal(K1) --for M2 computation
K=ideal(K2) --for M2 computation
--timing gens gb(J+K, Algorithm=>Sugarless)  --for M2 computation, takes .24 sec. in quotient ring
--timing gens gb(J, Algorithm=>Sugarless)  --for M2 computation, much harder,-- 218.467 seconds in quotient ring with sugar, 21 seconds sugarless

--
end

restart
load "Shidoku2.m2" 
loadPackage "RationalPoints"
timing rationalPoints J

timing G = gbBoolean(J+I) -- 9.5 seconds
loadPackage "RationalPoints"
GG = sub(G,R)
timing rationalPoints GG

timing G = gens gb(J, Algorithm=>Sugarless)  -- 4.3 seconds in grevlex, quotient ring
QS = S/(sub(ideal FP,S))
timing GG = gens gb(sub(G,QS), Algorithm=>Sugarless) -- 13.3677 seconds
timing gens gb(J, Algorithm=>Sugarless)  --  19 seconds in lex 

timing G = gens gb(J+I, Algorithm=>Sugarless)  --  4 seconds in grevlex
timing G = gens gb(J+I, Algorithm=>Sugarless)  --  21 seconds in lex
timing G = gens gb(J+I)  --  gRevLex 1.86 seconds 
timing G = gens gb(J+I)  --  Lex 2.15 seconds 
timing GG = gens gb(sub(G,S), Algorithm=>Sugarless) -- 7.30709 seconds
timing GG = gens gb(sub(G,S) ) --  .927 seconds
loadPackage "RationalPoints"
timing rationalPoints ideal GG -- 30 seconds

timing gens gb(J+I, Algorithm=>Sugarless)  --  21 seconds in lex





--Computations starting with DegRevLex, then convert to Lex to compare to gbBoolean
restart
R=ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4]
FP= {a1*(a1-1), a2*(a2-1), a3*(a3-1), a4*(a4-1), b1*(b1-1), b2*(b2-1), b3*(b3-1), b4*(b4-1), c1*(c1-1), c2*(c2-1), c3*(c3-1), c4*(c4-1), d1*(d1-1), d2*(d2-1), d3*(d3-1), d4*(d4-1), e1*(e1-1), e2*(e2-1), e3*(e3-1), e4*(e4-1), f1*(f1-1), f2*(f2-1), f3*(f3-1), f4*(f4-1), g1*(g1-1), g2*(g2-1), g3*(g3-1), g4*(g4-1), h1*(h1-1), h2*(h2-1), h3*(h3-1), h4*(h4-1), i1*(i1-1), i2*(i2-1), i3*(i3-1), i4*(i4-1), j1*(j1-1), j2*(j2-1), j3*(j3-1), j4*(j4-1), k1*(k1-1), k2*(k2-1), k3*(k3-1), k4*(k4-1), l1*(l1-1), l2*(l2-1), l3*(l3-1), l4*(l4-1), m1*(m1-1), m2*(m2-1), m3*(m3-1), m4*(m4-1), n1*(n1-1), n2*(n2-1), n3*(n3-1), n4*(n4-1), q1*(q1-1), q2*(q2-1), q3*(q3-1), q4*(q4-1), p1*(p1-1), p2*(p2-1), p3*(p3-1), p4*(p4-1)}
I=ideal(FP)
S=R/FP
K1={a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
K2 ={d1, d2, d3, d4-1, e1, e2, e3, e4-1, g1, g2-1, g3, g4, j1, j2, j3-1, j4, l1-1, l2, l3, l4, m1-1, m2, m3, m4}
J=ideal(K1) --for M2 computation
K=ideal(K2) --for M2 computation
timing withclue = gens gb(J+K, Algorithm=>Sugarless)  --.071735 seconds
timing noclue = gens gb(J, Algorithm=>Sugarless)  --4.03 seconds
RLEX=ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder => Lex]
inLex = sub(withclue,RLEX)  --puts in new ring with lex
timing  gens gb(inLex, Algorithm=>Sugarless) -- .019896
noclueLex = sub(noclue,RLEX)  --puts in new ring with lex
timing  sol = gens gb(noclueLex, Algorithm=>Sugarless) -- 11.2256


--gbBoolean computation
timing gbBoolean(J)  --took 10.881 seconds
K2 ={e1, e2, e3, e4-1, g1, g2-1, g3, g4, j1, j2, j3-1, j4, l1-1, l2, l3, l4, a4, b3, b4, c2, d2, d1, f2, f3, f4, h1, h2, h4, i1, i3, i4, k1, k2, k3, m3, m4, n3, q1, q2, p1}  --4 clue puzzle with implied packets
R=ZZ/2[a1,a2,a3,b1,b2,c1,c3,c4,d3,d4,e4,f1,g2,h3,i2,j3,k4,l1,m1,m2,n1,n2,n4,q3,q4,p2,p3,p4, MonomialOrder=>Lex] -- ring with removed implied packets
FP= {a1*(a1-1), a2*(a2-1), a3*(a3-1), b1*(b1-1), b2*(b2-1), c1*(c1-1),  c3*(c3-1), c4*(c4-1),  d3*(d3-1), d4*(d4-1),  e4*(e4-1), f1*(f1-1),  g2*(g2-1),  h3*(h3-1),  i2*(i2-1),  j3*(j3-1),  k4*(k4-1), l1*(l1-1),  m1*(m1-1), m2*(m2-1),  n1*(n1-1), n2*(n2-1), n4*(n4-1),  q3*(q3-1), q4*(q4-1),  p2*(p2-1), p3*(p3-1), p4*(p4-1)} --FP with implied packets from K2 removed
K1={a1+a2+a3-1,a1*a2, a1*a3,  a2*a3,   b1+b2+1,b1*b2, c1+c3+c4-1, c1*c3, c1*c4,  c3*c4, d3+d4-1,  d3*d4, e4-1, f1+1, g2+1, h3-1, i2+1, j3+1,  k4-1, l1+1, m1+m2-1,m1*m2,  n1+n2+n4-1,n1*n2,  n1*n4, n2*n4,  q3+q4-1,  q3*q4, p2+p3+p4-1, p2*p3, p2*p4, p3*p4, a1+b1+c1-1,  a1*b1, a1*c1,  b1*c1,  a2+b2+1, a2*b2,a3+c3+d3-1,  a3*c3, a3*d3,  c3*d3,c4+d4-1, c4*d4,f1-1, g2+1,  h3-1,  e4-1, l1-1,  i2-1,  j3-1,  k4-1,  m1+n1+1, m1*n1,  m2+n2+p2-1, m2*n2,  m2*p2,  n2*p2,q3+p3-1,  q3*p3,n4+q4+p4-1,  n4*q4, n4*p4, q4*p4,a1+m1-1,  a1*m1,  a2+i2+m2-1, a2*i2, a2*m2,  a3+1,  e4-1,  b1+f1+n1-1, b1*f1,  b1*n1,  f1*n1,  b2+n2-1,  b2*n2,    j3-1, n4-1,  c1-1,  g2-1,  c3+q3-1,  c3*q3, c4+q4+k4+1,  c4*k4, c4*q4, k4*q4, l1-1, e1-1, b1*e1,e2+f2-1,e2*f2, b3+e3+f3-1, b3*e3, b3*f3, e3*f3, a4+b4+f4-1, a4*f4,a4*b4, b4*f4, d1+g1+h1-1, d1*h1, d1*g1, g1*h1, c2+d2+h2-1, c2*d2, c2*h2, d2*h2, g3-1, g4+h4-1, g4*h4, i1+j1-1, i1*j1, j2-1, i3+m3+n3-1, i3*n3, i3*m3, n3*m3,i4+j4+m4-1, i4*j4, i4*m4, j4*m4,l1-1,  p2-1, q3+p3-1, q3*p3, k4+q4+p4-1, k4*q4, k4*p4, q4*p4} --K1 without implied packets

--playing with packets
restart
R=ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder=>Lex]
K1={a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
K2 ={p2, p3, p4, q1, d1, h1, k1, j1, l1, m1, n1}  -- 10 clue packets implied by p1=1
K2={a1, f1, k1, p1}
K2={a1, a2, e1, i1, b1, b2, g3, q3}
J=ideal(K1) 
K=ideal(K2)
timing gbBoolean(J+K)  --time .03 seconds
timing gbBoolean(J)  --time 10.669 seconds
--Computations for the same shidoku puzzle, except with only 16 variables and over Q, not ZZ/2.

restart
R=QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p, MonomialOrder=>Lex]
K1 = {(a-1)*(a-2)*(a-3)*(a-4), (b-1)*(b-2)*(b-3)*(b-4),(c-1)*(c-2)*(c-3)*(c-4), (d-1)*(d-2)*(d-3)*(d-4),(e-1)*(e-2)*(e-3)*(e-4), (f-1)*(f-2)*(f-3)*(f-4),(g-1)*(g-2)*(g-3)*(g-4), (h-1)*(h-2)*(h-3)*(h-4),(i-1)*(i-2)*(i-3)*(i-4), (j-1)*(j-2)*(j-3)*(j-4),(k-1)*(k-2)*(k-3)*(k-4), (l-1)*(l-2)*(l-3)*(l-4),(m-1)*(m-2)*(m-3)*(m-4), (n-1)*(n-2)*(n-3)*(n-4),(o-1)*(o-2)*(o-3)*(o-4), (o-1)*(o-2)*(o-3)*(o-4), a+b+c+d-10,a*b*c*d-24, e+f+g+h-10, e*f*g*h-24, i+j+k+l-10, i*j*k*l-24,m+n+o+p-10, m*n*o*p-24, a+e+i+m-10, a*e*i*m-24, b+f+j+n-10,b*f*j*n-24, c+g+k+o-10, c*g*k*o-24, d+h+l+p-10, d*h*l*p-24,a+b+e+f-10, a*b*e*f-24, c+d+g+h-10, c*d*g*h-24, i+j+m+n-10,i*j*m*n-24, k+l+o+p-10, k*l*o*p-24}
K2 = {d-4, e-4, g-2, j-3, l-1, m-1}

J=ideal(K1)
K=ideal(K2)
timing gens gb(J+K) --0.002367 seconds
timing G = gens gb(J, Algorithm=>Sugarless)  --6.89729 seconds
RLex=QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p, MonomialOrder=>Lex]
Glex = sub(G, RLex)
timing gens gb Glex




