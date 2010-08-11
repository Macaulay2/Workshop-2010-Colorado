
------------
-- Keywords -- 
-- position: "find", "find Element"

-- every page in the documentation should have the search bar instead of going back to index

-- lex order takes longer than several minutes (it never finished for me) 
restart
R=QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p, MonomialOrder=>Lex]
K = ideal {(a-1)*(a-2)*(a-3)*(a-4), (b-1)*(b-2)*(b-3)*(b-4),(c-1)*(c-2)*(c-3)*(c-4), (d-1)*(d-2)*(d-3)*(d-4),(e-1)*(e-2)*(e-3)*(e-4), (f-1)*(f-2)*(f-3)*(f-4),(g-1)*(g-2)*(g-3)*(g-4), (h-1)*(h-2)*(h-3)*(h-4),(i-1)*(i-2)*(i-3)*(i-4), (j-1)*(j-2)*(j-3)*(j-4),(k-1)*(k-2)*(k-3)*(k-4), (l-1)*(l-2)*(l-3)*(l-4),(m-1)*(m-2)*(m-3)*(m-4), (n-1)*(n-2)*(n-3)*(n-4),(o-1)*(o-2)*(o-3)*(o-4), (o-1)*(o-2)*(o-3)*(o-4), a+b+c+d-10,a*b*c*d-24, e+f+g+h-10, e*f*g*h-24, i+j+k+l-10, i*j*k*l-24,m+n+o+p-10, m*n*o*p-24, a+e+i+m-10, a*e*i*m-24, b+f+j+n-10,b*f*j*n-24, c+g+k+o-10, c*g*k*o-24, d+h+l+p-10, d*h*l*p-24,a+b+e+f-10, a*b*e*f-24, c+d+g+h-10, c*d*g*h-24, i+j+m+n-10,i*j*m*n-24, k+l+o+p-10, k*l*o*p-24}
timing G = gens gb(K)  -- this did not finish for me

-- this one is really slow in lex order over ambient R
-- valence 5
restart
R = ZZ/2[ vars(1..36), MonomialOrder=>Lex]
--QR = R / ideal apply(gens R, x -> x^2 + x)
I = ideal(i*r*B+i*s*C+s*B*C+i*s+s*B+B*C+s,b*f+b*o,c*F*J+E*F*J+c*E+C*J+F*J+c+C+F,k*o*p,k*z*F+k*z*G+F*G+F+G,e*f*x*J+e*f*t+e*t*x+e*x+e*J,f*m*p+m*p*y+f*m*J+J,i*t*A*B+i*t*A*G+t*A*B*G+t*A*B+A*B*G+i*B+i+A,e*y*z+e*y,h*k*D*I+h*k*E*I+k*D*E+k*D*I+D*I,f*m*v*I+d*v*I+d*f+d*m+I,e*x+k*x+k*E+n*E+k+E,e*z+e,o*y,e,i*y*F*K+e*i*F+i*y*F+e*i*K+e*y*K+e*y+i*F+i*K,d*e*i*u+u,d*f*s*C,i*k*n*t+i*k*n*J+i*n*t+k*n*t+i*t*J+i+J,e*s*F+s*u*H,h*q*r*B*H+h*q*r*B+h*B*H,d*v*A*E+d*e*v+e*v*A+d*A*E+e*A*E+e*v,b*r*B*H+b*r*G*H+b*r*B+r*B*G+b*G*H+b*B+B*G+G*H,b*g*m*r*s+b*g*s+b*r*s+b*r+m*r+m*s+b+s,h*m*u*B+h*u*H+m*B*H+h*m+u*H,f*g*n+c*n+c+g+n+1,e*m*o*r*I+e*m*o*r+e*m*r*I+e*m+o,x*A*K,c*g*z*B+c*g*B+g*z*B+z*B+g*C+g,i*n*t*J+i*n*t+g*t+t*J+i+n,j+r+1,s*v*y*I+s*y*I+y*F*I+F*I+F+I,e*h*m*q*v+e*h*m*q+e*h*q+e*m*v+h*m*v+e,k*r*A*G+r*x*G+G,b*e*H*I+b*g*H*I+e*H*I,E*F*G*H)
gens gb I -- I was not patient enough to wait for this 


-- this one is kind of slow in Lex order, maybe you can use it to improve the algorithm
--Next computations in a quotient ring with 20 variables.
--valence: 5
restart
R = ZZ/2[ vars(1..20), MonomialOrder=>Lex]
FP = ideal apply( gens R, x -> x^2+x)
I = ideal (d*h*j + h*j*o + d*k*o + j*k*o + d*k + d + h, e*f*o*q + e*g*o + f*g*o + e*g + f*q + g*q + g + 1, h*l*n + j*n*r, q*u + f + q + 1, b*j + h*n, l*m*o + l*q, f*h*o*q + f*h*o + f*o*t + h*q*t + h + 1, g*h*p*r + g*h*r + g*p*r + h*p*r + g*r + h*r + p*r + h + m, d*k + d*r + f*r + k, b*j*o*p*s + b*j*p*s + b*j*p + b*o + b + p + 1, g*r, e*j*r*s + o*r*s + o*r + r*s + e + j + s, m*u + n*u, i*j*p*q + h*i + h*p + j + q, e*l*t*u + d*e*l + e*l*t + d*l*u + e*l*u + d, e*l*m*r + e*l*m*s + l*m*r + l*r*s + m*r*s + l*m, j*m*q*r*t + j*m*q + j*m*t, b*d*r*u + d*p*r*u + d*p*u + b*p + d*p + b*r + p, c*e*m*s, d*e*q*u + e*u + q*u + q)
time gens gb(I+FP) -- 14.8312 seconds.

-- 


-- here Algorithm=>Test does not work
-- Lex order in quotient ring
-- Sugarless 20 seconds
-- Sugar 200 seconds
-- Test > 200 seconds :( 
restart
S = ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder=>Lex]
QR = S / ideal apply(gens S, x -> x^2+x)
  II0 = ideal {a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
  gens gb (II0, Algorithm=>Sugarless)

