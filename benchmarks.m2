
restart

loadPackage "BenchmarkGb"
--installPackage "BenchmarkGb"
--loadPackage "BooleanGB"

makeRing = method()
makeRing (ZZ,ZZ) := (nvars,c) -> (
  ll := apply( (1..nvars), i -> value concatenate("x",toString i));
  R1 :=ZZ/c[ll];
  --R1 := ZZ/2[vars(0..nvars-1), MonomialOrder=>Lex];
  L := ideal apply(gens R1, x -> x^c-x);
  R1/L
)


-- Computations for Shidoku with Boolean polynomials.  J are the shidoku polynomials and K is a set of initial clues to give a unique answer.

S = ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder=>Lex]
II0 = ideal {a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
II00 = ideal {d1, d2, d3, d4-1, e1, e2, e3, e4-1, g1, g2-1, g3, g4, j1, j2, j3-1, j4, l1-1, l2, l3, l4, m1-1, m2, m3, m4}

shidokuNew :=ideal {a1+a2+a3+a4-1,a1*a2, a1*a3, a2*a3,  b1+b2+b3+b4-1,b1*b2, b1*b3, b2*b3, c1+c2+c3+c4-1,a1*a2, c1*c3,  c2*c3,   d1+d2+d3+d4-1,d1*d2, d1*d3,  d2*d3, e1+e2+e3+e4-1,e1*e2, e1*e3,  e2*e3,  f1+f2+f3+f4-1,f1*f2, f1*f3,  f2*f3, g1+g2+g3+g4-1,g1*g2, g1*g3,g2*g3,  h1+h2+h3+h4-1,h1*h2, h1*h3, h2*h3, i1+i2+i3+i4-1,i1*i2, i1*i3,  i2*i3,  j1+j2+j3+j4-1,j1*j2, j1*j3, j2*j3, k1+k2+k3+k4-1,k1*k2, k1*k3,  k2*k3,  l1+l2+l3+l4-1,l1*l2, l1*l3, l2*l3, n1+n2+n3+n4-1,n1*n2, n1*n3,  n2*n3, n2*n4,  q1+q2+q3+q4-1, q1*q2, q1*q3, q2*q3, p1+p2+p3+p4-1,p1*p2, p1*p3,  p2*p3, a1+b1+c1+d1-1,  a1*b1, a1*c1, b1*c1, a2+b2+c2+d2-1, a2*b2, a2*c2, b2*c2, a3+b3+c3+d3-1, a3*b3, a3*c3, b3*c3, a4+b4+c4+d4-1, a4*b4, a4*c4,  b4*c4, e1+f1+g1+h1-1, e1*f1, e1*g1, f1*g1, e2+f2+g2+h2-1, e2*f2, e2*g2, f2*g2, e3+f3+g3+h3-1, e3*f3, e3*g3, f3*g3, e4+f4+g4+h4-1, e4*f4, e4*g4,  f4*g4, i1+j1+k1+l1-1, i1*j1, i1*k1, j1*k1,  i2+j2+k2+l2-1, i2*j2, i2*k2, j2*k2,  i3+j3+k3+l3-1, i3*j3, i3*k3,j3*k3, i4+j4+k4+l4-1, i4*j4, i4*k4, j4*k4,  m1+n1+q1+p1-1, m1*n1, m1*q1, n1*q1,  m2+n2+q2+p2-1, m2*n2, m2*q2, n2*q2, m3+n3+q3+p3-1, m3*n3, m3*q3, n3*q3, m4+n4+q4+p4-1, m4*n4, m4*q4,  n4*q4, a1+e1+i1+m1-1, a1*e1, a1*i1, e1*i1,  a2+e2+i2+m2-1, a2*e2, a2*i2, e2*i2,  a3+e3+i3+m3-1, a3*e3, a3*i3,e3*i3, a4+e4+i4+m4-1, a4*e4, a4*i4,  e4*i4,  b1+f1+j1+n1-1, b1*f1, b1*j1,f1*j1, f1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2,f2*j2,  b3+f3+j3+n3-1, b3*f3, b3*j3, f3*j3, b4+f4+j4+n4-1, b4*f4, b4*j4, f4*j4,  c1+g1+k1+q1-1, c1*g1, c1*k1, g1*k1,  c2+g2+k2+q2-1, c2*g2, c2*k2,  g2*k2,  c3+g3+k3+q3-1, c3*g3, c3*k3, g3*k3,  c4+g4+k4+q4-1, c4*g4, c4*k4,  g4*k4,  d1+h1+l1+p1-1, d1*h1, d1*l1,  h1*l1, d2+h2+l2+p2-1, d2*h2, d2*l2,  h2*l2, d3+h3+l3+p3-1, d3*h3, d3*l3, h3*l3,d4+h4+l4+p4-1, d4*h4, d4*l4,  h4*l4,  a1+b1+e1+f1-1,  a1*e1, a1*b1, b1*e1, a2+b2+e2+f2-1, a2*b2, a2*e2, b2*e2,a3+b3+e3+f3-1, a3*b3, a3*e3,b3*e3,  a4+b4+e4+f4-1, a4*b4, a4*e4, b4*e4,c1+d1+g1+h1-1, c1*d1, c1*g1, d1*h1,  d1*g1,c2+d2+g2+h2-1, c2*h2, c2*d2, c2*g2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, d3*g3,  c4+d4+g4+h4-1, c4*d4, c4*g4,  d4*g4,  i1+j1+m1+n1-1, i1*j1, i1*m1,  j1*m1,  i2+j2+m2+n2-1, i2*j2, i2*m2,  j2*m2,  i3+j3+m3+n3-1, i3*j3, i3*m3,  j3*m3, i4+j4+m4+n4-1, i4*j4, i4*m4,  j4*m4, k1+l1+q1+p1-1, k1*l1, k1*q1,  l1*q1,  k2+l2+q2+p2-1, k2*l2, k2*q2,  l2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3,  l3*q3,  k4+l4+q4+p4-1, k4*l4, k4*q4, l4*q4} 


------------------
-- randomly generated

-- valence 5
R = ZZ/2[ vars(1..36)]
QR = R / ideal apply(gens R, x -> x^2 + x)
II1 = ideal(i*r*B+i*s*C+s*B*C+i*s+s*B+B*C+s,b*f+b*o,c*F*J+E*F*J+c*E+C*J+F*J+c+C+F,k*o*p,k*z*F+k*z*G+F*G+F+G,e*f*x*J+e*f*t+e*t*x+e*x+e*J,f*m*p+m*p*y+f*m*J+J,i*t*A*B+i*t*A*G+t*A*B*G+t*A*B+A*B*G+i*B+i+A,e*y*z+e*y,h*k*D*I+h*k*E*I+k*D*E+k*D*I+D*I,f*m*v*I+d*v*I+d*f+d*m+I,e*x+k*x+k*E+n*E+k+E,e*z+e,o*y,e,i*y*F*K+e*i*F+i*y*F+e*i*K+e*y*K+e*y+i*F+i*K,d*e*i*u+u,d*f*s*C,i*k*n*t+i*k*n*J+i*n*t+k*n*t+i*t*J+i+J,e*s*F+s*u*H,h*q*r*B*H+h*q*r*B+h*B*H,d*v*A*E+d*e*v+e*v*A+d*A*E+e*A*E+e*v,b*r*B*H+b*r*G*H+b*r*B+r*B*G+b*G*H+b*B+B*G+G*H,b*g*m*r*s+b*g*s+b*r*s+b*r+m*r+m*s+b+s,h*m*u*B+h*u*H+m*B*H+h*m+u*H,f*g*n+c*n+c+g+n+1,e*m*o*r*I+e*m*o*r+e*m*r*I+e*m+o,x*A*K,c*g*z*B+c*g*B+g*z*B+z*B+g*C+g,i*n*t*J+i*n*t+g*t+t*J+i+n,j+r+1,s*v*y*I+s*y*I+y*F*I+F*I+F+I,e*h*m*q*v+e*h*m*q+e*h*q+e*m*v+h*m*v+e,k*r*A*G+r*x*G+G,b*e*H*I+b*g*H*I+e*H*I,E*F*G*H)

R = ZZ/2[ vars(1..20)]
QR = R / ideal apply(gens R, x -> x^2 + x)
II2 = ideal (n*p*s + c*p + n + p + s, c*e*i*s + e*i*s + c*f + c*i + f*s + e, d*g*i*r + d*g*r*u + d*g*i + d*r + u, d*e*f + d*f + 1, g*h*l*m + g*h*l + h*l*m + g*h + g*m + h*m, e*g*n*q + g*n*q + e*r + e + n, c*d*n + c*m*n + c*m + d*m + h*m + h*n, c*e*f*p + c*d*e + d*e*f + d*e*p + c*d + f*p + e + f, b*j*p + f*j + b*p + f*q, g*h*n*o + g*n*o*t + g*n*t + h*o + g + 1, d*j*s*t + j + o + t, c*l*m*t + c*l*t + k*l*t + l*m*t + m*t, d*i*m, b*g*i*j + b*i*j + f*i*j + f*i + i*j + i + j, g*o*q + g*o + f + o + 1, d*g*n*o + e*g + n, c*i*k*t + c*k*t + c*k*u + k*t*u + c*u + t, c*i*q*t + c*i*s + i*s*t + i*s + q*t + i, c*h*p + n*p*u, f*i*j*q + f*i*l*q + f*j*l*q + f*i*l + i*l*q + i*j + j*l + f*q)

II3 = ideal (c*k*r + 1, b*d*h*i*n + b*h*i*n + b*d*h + b*d*i + b*i*n + d*n + b, g*h*l*o*r + g*o, j*l*m + d*m*t + l*m*t + l*t, e*k*t*u + g*k*t*u + e*g*k + e*g*u + g*k + u, m*n*q*r + k*n + n*q + m*r + 1, b*e*g*o + e*g*o*s + b*g*o + e*g*o + b*o*s + e*o*s + e*g, e*g*k*q + g*k*q*t + g*k*q + g*t + k*t, j*m*t*u + f*j*t, o*q*t*u + o*t*u, p*s*u + q*r + r*s + q + u, b*s, b*f*n*s + f*n*s + n*s*t + f*n + f, d*p + d*t, g*l*q*t + q*t, c*d*e*p*q, d*q*r*t + o*q*r + d*q + o*r + r*t + o, d*h*m*n*p + h*m*n*p, f*k*o*s*t + f*k*o*s + f*o*s*t + k*o*s*t + f*k*o + f*k*s + f*k*t + f*k + o*t + f, k*q*t + h*q + h + 1)

II4 = ideal (d*h*j + h*j*o + d*k*o + j*k*o + d*k + d + h, e*f*o*q + e*g*o + f*g*o + e*g + f*q + g*q + g + 1, h*l*n + j*n*r, q*u + f + q + 1, b*j + h*n, l*m*o + l*q, f*h*o*q + f*h*o + f*o*t + h*q*t + h + 1, g*h*p*r + g*h*r + g*p*r + h*p*r + g*r + h*r + p*r + h + m, d*k + d*r + f*r + k, b*j*o*p*s + b*j*p*s + b*j*p + b*o + b + p + 1, g*r, e*j*r*s + o*r*s + o*r + r*s + e + j + s, m*u + n*u, i*j*p*q + h*i + h*p + j + q, e*l*t*u + d*e*l + e*l*t + d*l*u + e*l*u + d, e*l*m*r + e*l*m*s + l*m*r + l*r*s + m*r*s + l*m, j*m*q*r*t + j*m*q + j*m*t, b*d*r*u + d*p*r*u + d*p*u + b*p + d*p + b*r + p, c*e*m*s, d*e*q*u + e*u + q*u + q)

II5 = ideal(l,c*g*h*k*q+c*h*k*q+c*k*q+h*k*q+g*k+h*q+k+1,b*f*k*q*t+b*f*k*t+b*t+q,c*d*j*k+c*d*j*t+c*d*k*t+d*j*k+j*k*t+d*j+j*k+j,e*j*p*q*u+e*j*q*u+e*j+e*q+p*q+q,c*k*m*s*u+c*k*m*u+c*k*m+k*m*s+k*m*u+k*u+m*u+m,b*f*g*r+e*f*g*r+e*f*r+f*g+e*r,f*k*l*u+i*k*l*u+f*l*u+k*l*u+i*k+i*l+k*l+k,f*l*o+f*n+l*o+n*o+l*u,d*e*g*n+d*n+g,d*j*m*o+d*e*o+d*o+m*o+1,f*g*h*i+f*g*h+f*g*i+f*g*q+h*i+1,d*p*r*s+d*p*s+f*r+f*s+f,b*j*k*q*r+b*j*k*q+j*k*q*r+b*q,d*f*g*n+d*f*p+f*n*p+g*n*p+d*g+g*p+1,k*p*q,h*l*o+h*n*r+h*o*r+l*o*r+n*o*r+l+o,f*p*u+c*f+p*u+1,d*h+d,b*g*h+h)

II6 = ideal(b*c*e*j+b*c*j*n+b*e*j*n+c*e+c*n+c,g*k+g,d*e*f*o+d*f*o*r+d*f*o+e*f*o+d*e*r+e+1,f*s+n*s,d*e*j*o+d*e*j*q+d*j*o*q+e*j*o+d*j*q+e*o+d+o,f*i*n+f*n,f*j*l*p+f*j+j*l,e*k*n*s+e*g*s+e*n*s+g*s+g,c*p*s*t+c*j*t+s,c*k+f,b*e*f+b*e*o+b*o*t+e*o*t+b*o+f*o,b*g+f*q+q,i*m+b*t+k,e*i*l+e*i*m+h*i+h*m+e+1,r*t+1,d*m,d*f*p+e*p*q+f*p*q+d*f+d*p,e*i*m+e*i*p+i*m*p+e*m+f*p+f+i+p,e*g*h*i*u+g*h*i*u+g*h+h*i,c*q+i*q)


idealList = {II0, II0+II00, II3, II4, II5, II6}
--idealList = {II3, II0+II00, II5, II6, II0, II4, II2}
--idealList = {II3, II0+II00, II5, II6, II0, II4}
idealList = {II0, II0+II00, II1, II2, II3, II4, II5, II6}
idealList = {II0, II0+II00, II2, II3, II4, II5, II6}

S1 := ideal (1, d + 1, b, 0, u + 1, r, 1, 1, b + 1, 0, j, 1, k + 1, r + 1, c, 0, s, r, 1, u + 1)
--.003734	.0019	.002175	.001726	.000062	

S2 := ideal (b*k + b + k, 1, j*t, q, t*u + t + u + 1, 1, j, 1, h + 1, 1, c, o*q + o + 1, e + p, h*k + 1, b + j + 1, d*m + d, b + l + 1, j, 1, j + u + 1)
-- .002599	.002257	.001333	.002552	.000012	

S3 := ideal (d*k*s + d*s + k*s + d + k, f*r, e + r, e*i*q + i*q, b*g + b + q, e*f*u + u, m*o*p + m*o + m*p + o*p + 1, f*g*r + f*r + 1, f*h*n + f*h + f, g*p + l*p, d*h*u + d*h + d*u + d + h + u, m, n*r + n*s + r*s + r + 1, n*o*u + n*o + n*u + o, j*r + 1, i*j + j + u + 1, c*r + o*r + 1, n*p*r + p*r, c*e*f + c*e + e, u)
--.004745	.001999	.004495	.001888	.000009	

S4 := ideal (b*m*p + b*m + p + 1, c*e*g*p + c*e*g + e*g + g*p, c*i*q + q*r + q, f*i*k*l + i + l, b*c*j + b*j + c*l + l + 1, h*n*r + 1, e*f*t + e*f + f*t + t*u + t, r, l*n*s + l*m, j*r*u + j*r + r + u, m*o, c*d*s + b + d, h*l*u, c*n + c*p, l*r + m*r, l*u, m*o, c*l*s + j*l*s + l + s, e*h*j*o + e*h*j + e*j*o + e*o + h + 1, k*n*p + k*n*t + k*p*t + k*n + n*t + n + p)
--.004284	.001855	.00196	.001843	.00001	

S5 := ideal (b*j*o + b*j*q + c*j*q + b*o*q + c*o*q + c*q, k*p*q*r + o*q*r + p*q*r + p*q + k*r + o*r, i*p*t + t, d*g*h*s*t + d*s*t + h*s*t + g + t, c*e*h*t + e*h*n*t + e*h*t, c*o, g*h*n*r + g*n*r*s + h*n + r*s + h + r + s, e*o*r, l*n*o*u + f*l*n + f*l*o + l + n, i*o + f*q + q, k*p*r*s*t + p*s, b*l*n*o*q + b*l*n*o + b*l*o + b*n*o + b*n*q + b*o*q + o + q, f*k*r*s + k*r*s*u + f*k*s + k*r*s + f*r + f*u + k*u, c*j*m*r + c*m*r + j*q*r + c*j + j*q + m*q, b*g*q*s + g*n*q + b*g + b*s + g*s + b, h*i*k*t + h*i*t + k*o*t + h*i + h*t, i*k*m*t + i*k*q*t + k*m*q*t + i*k*m + i*k*t + k*m*t + k*q*t + k*q + m, b*f*i*q + b*f*i + b*i*j + b*f*q + b*q + f + i, d*k*r + e*k*r + b*d + b*k + b, h*k*p + h*l*p)


R = ZZ/2[ vars(1..30)]
SS1 = ideal (k + 1, 1, y, B + 1, B, 1, k + 1, 1, n + 1, n, i + 1, 0, h, 1, 1, j, h, D, 1, e, 0, 0, 0, s + 1, 0, C, 0, 0, 0, 0)
-- .002832	.002247	.002892	.003013	.000069	

SS2 = ideal (1, w + E, z*A + z + 1, b*D + 1, j*q, g*s, r*A, c*j + j + 1, v + 1, A + 1, b*e + b + e + 1, r + 1, E, g*x, o, g + r + 1, m, e*l + l + 1, v, j + E, n*D + 1, b + d + 1, 1, s*w + w, j*r + j + 1, 1, o*r, k*m + k + 1, h*w + w, E)
--.003257	.002565	.001621	.002553	.000008	

SS3 = ideal (1, b*e*h + b*e + e*h + b, b*l*p + b*p + l*p + b + p, b*d*e + b*d + b*e + e, s*x*y + x + y, d*r + d*E + r*E + E + 1, 0, q*u + u, e*h*t + e*h + 1, w*C*E + w*C + E, f*m*p, d*k*C + k*C + d + C + 1, e*u*z + u*z + u + z, e*E + e + 1, 1, e, c*k*o + c*k + c*o + k + 1, l*r*E + l + E + 1, k*p + p + q, g*A*B + g*A + g*B + g + A, g*q*D + g*q + g*D + g + q + 1, x*C*E + E, 1, l*q + l*w + q*w + l + w + 1, p*y*B + p*y + y*B + p + 1, t*v*B + t*B + v + B, e + s + x, i, x, c*v*z + 1)
--.005078	.002314	.003152	.003554	.000015	


SS5 = ideal (k*w + 1, h*n*C*E + c*h*n + c*h*E + h*C + h*E + C, n*p*v*w + p*s + n*v + p*w, g*p*q*u*B + g*p*q + g*u*B + q, e*k*o*E + k*v*E + e, b*h*k*n*o + k*n + b*o + k + n, m*q*w + p*w*B + m*p + w*B + w, b*f*i*q*t + b*f*i*t + f*i*q*t + b*f*i + i*t + b + 1, g*o*y + g*p*A + g*o, d*j*m*s*u + d*j*m*u + d*j*s + d*m*s + j*m*u + j*s*u + m*u + 1, c*q*u*z + c*q*x*z + c*u*x*z + q*u + c*z + u*z, g*y*z*D + g*h*y + g*z + y, b*c*k*C + b*k*C*E + b*c*E + C*E, i*l*q + f*p*q + q, b*j*s*v + l*s + j, b*g*t + g*h*x + g*t + g*x + t, y*B*E + w*A + w*E + B + 1, c*j, c*k*o*u*w + k*o*u*w + c*u + o*u + c*w + w + 1, d*y, d*q + d*B, f*p*w + f*z*D + w*z*D + f*p, c*i*j*s*D + c*i*s*D + c*i + i*s + c*D + c, e*l*A + l*n*A + c*e + c*n + e*n + c, f*k + f*B + z*B + f + 1, x, f*r*u*w + f*q + q*u + r*w + q, c*l, c*m*n*A + h*m*n*A + c*m*n + h*m*n + h*n*A + m*n + c, d*f*o*q*r + d*f*o*r + f*o*q*r + d*f*q + d*f*r + f*q*r + o*q*r + q + 1)
--.071554	.002752	1.21457	.00349	.041698	


s1 =ideal (e*m*q + e*q, g + 1, p*r*A + r, A, f*l + l*s, 0, w + 1, c*n + n, d*m*y + d*y, e*l + e*s + l*s + l, k, c*y + c + y, f + i + l + 1, l, c*d*v + v, 0, e, g*k, v*B + 1, e*l*x + e*x, d, e*m + d + e + m, c*y, b*l, l*p + l*t + l, d*h*x, b*B*D + B*D + 1, h*m*x + m*x, f*l*r + l, h*m*o + h*o)
--.000187	

s2 = ideal (r*v*y + r*v + v*y + r + v, g, k*w*E + k*E + w*E + w, g*m, s, l*D + A*D + A, r*t*y + t*y, f*z*B + z, j*s*x + j*s + s*x + j + s, n*x + n*E + x*E + 1, k*o + o*z + k + 1, c*d*B + c + B + 1, i*y + u*y + y + 1, e*C + e*D + e + 1, d*e + d*k + e*k + e + k, k*A + k + A + 1, f*q + q + 1, v*w + v + w + E + 1, c*j*p + c*j + c*p + c + p, x, k*t*u + k*u + t*u + t, g*v + i*v + v + 1, e*B + o*B, 0, b*u + b + 1, b*j + b*A + A, p*C, i*s*v + i*s + i*v + s*v, 0, k*v + k*E + v*E + v + 1)
-- .000596	

s3 = ideal (1, D, 1, B + 1, s + 1, 0, g + 1, 1, 1, 0, x + 1, q, 0, d, m, 1, b, 0, e, f, d, 0, z, y, 1, f, 0, 0, 1, f)
--.000191	

s4 = ideal (p + C, b, z + 1, C*D + 1, z + 1, k*z + 1, c*E + E + 1, 0, j*o + o, f*n + f + 1, 1, t*u, f*t + t + 1, x, c*C + 1, t*x, c + 1, 1, d + j, 0, 0, o + 1, f*n + f + n + 1, i*z + i + z, c*u, d*D + d + D + 1, 1, b, p*q + p + q + 1, e*m)
--.000584	

s5 = ideal(h*p*q+p*w+q*w+h*C+q*C,c*g*C*E+c*g+c*C+s*E+c,h*m*A*C+h*m*B+m*C+C,h*o*p+h*p*t+h*o,i*w*D,k*r*E+k*E+r*E+v,c*k*n*w*C+c*k*n*w+c*n*w,e*g*k*t+g*k*t,r*u*v*y*E+u*v*y*E+r*u*E,k*u,h*p*s+d*p*u+p*u,e*f*j*q*x+e*f*q*x+j*q*x+f+1,s*u*A*D+s*D+u+D,d*k*m*t+d*t*C,f*s,c*d*f*g*j+c*g*j+f*g*j+c*j+g,i*j*r+j*m*B+j*m+m*B+r,c*C+v,0,1,f*t*z*C+f*t*C+t*z,k*l*r+l*r*u+k*r+k+l,c*A,e*j*l*q*u+e*j*q+j*q*u+l*u,f*t+c*A+t*A+f,d*p*q*z,d*t,e*r*y*z*B+e*r*y*B+r*y*z*B+r*y*B,b*d*k*t+b*k*p*t+b*k*t+d*p*t+b*k,b*e*p*w+b*i*w+e*w+b)
-- gbBoolean:      .000188 seconds.

s6 = ideal(m*n*E+w*D*E,b*i*D+p*D+x*D,i*p*t,l+p,c*j*t,d*h*o*r,r*w+w,d*g*h*m+g*h*m,l*z*A+1,b*l*z+l*z,f*g+f*o+l*o,b*k*o*r+k*o*r+b*r,o*p*E,p+1,m*A,h*j*m*x,r*t*B,m*v+b,h*B*E+h*E,h*w*A,d*e*h+e*h*t+e*h+h*t,f*j*l*m*A+f*j,d*w,k*m*p*z+j*k*p,i*u,c*i*o*r+c*i*o+c*i*x+c*o*x,v*B,u*v*E+p*E+E,b*l*p*B+b*l*B,i*v*A*D)
-- gbBoolean:      .000815 seconds.

s7 = ideal(h*r*B*D+h*r*w+h*w*D+w*B*D,e*h*u+b*u*z+b*z+1,q*u+q*C,c*e*m*D+m*s*D+c*m+e*m+c*D,b*i*l*v+i*s*v+i*s+b,f*B+h,j*k*o+k*o*C+g*o,b*i*C,d*m+d*u+m*u,b*h*r+b*r+B+1,g*z*D+m*z+k+D+1,c*l*u+c*A,c*i*p*s+c*i*p+c*p+e*p,e*i*m*D+e*i+m*n+m*D+D,h*p*s*y*A+p*y*A+p*s+p,c*l*x*B*C+c*x*B*C+c*l*B+l*x*B+l*x+x*C,d*h*o*t+h*k*o+o,g*r*z+e*g*B+g*r*B+r,e*f*x*y+f*x*y*A+e*f*A+f*y*A+x*y*A+e*A,d*j,j*k*m*z+j*k*m*D+m*z*D+k*D,k*p*w*E+k*q*w*E+k*w*E+p*E+q*E+1,j*k*q+j*q*x+q*u*x+j*k,e*m*s+b*c,j*p*t*z+p*s*t*z+j*p*s+p*t*z,e*y,l*n*q*r*z+l*n*r*z+1,g*l*w*D+g*r*w*D+w*D,n*v*y*E,c*e*r*s+e*l*r*s+e*r*s+e*s)
--gbBoolean:      .223801 seconds.

--valence: 6
s8 = ideal(f*p*t*A+p,b*g*i*m,j*v*C,d*e*o*s+d*s,b*j*m,b*y*A+b*p,e*l*C+e*p,o*v,o*u*A*D+A,p,b*x*A+b*x,b*f*o*r,b*d*B,e*h*n*v*y+c*h*y,f*n*z*E+m*u*z*E,k*q*s+q*s*y,e*y*A*C*E,p*q,e*B*D,j*l*m*D,g*j*r*x*B+l*x*B,e*h*w+j,c*l*t*v*x*B,C*E+e,d*g*m*p*t*A+d*g*m*A,d*t*u*y+j*t*w,h*C,n*u*C+n,g*z*D+D,h*l*q*r*z)
-- gbBoolean:      .082425 seconds.

--valence: 7
s9 = ideal(f*A,g*B,p*r*v,c*o*t+d,m*q*s*C*D+b*C*D+m+C,g*h*l*x,j*l*n*o*p+g*j*n*o,1,k*l*s*E+k*t*E,k*p*t*z*A*D+k*t,n*s*v*B+s*t*v+d,j*o*r*x*B*C*D+j*o*x*C+o,c*f*l*o*B+c*i*o*t+f*t*B,s*x*C*D+x*A*C,e*f*g*l+e*g*l*r+e*g*r*A+f,i*j*x*A*D*E+d*j*x*A*D+j*A*D,e*f*o*s*w*D+e*w+c*D,c*e*m*n*v+e*m*n*v+c*m*x*B+e*m*B,e*l*m,f*g*l*x*D,b*o*r*x*A+b*n*o*v+r*v*x*A+A,h*i*k*s*v*D+h*i*k*s*A+i*k+s*D,g*w*B+g*z+w*B,c*n*t*x+c*i*t+e*t*x+e*t*z,d*m*q*C,o*y,i*m*p*t*A+b*i*x*A+p*x*A+1,l*n*q*w,d*k*A,d*f*g*u*B+d*f*v*A*B+f*u*v+f*g*A)
-- gbBoolean:      .000573 seconds.

s10 = ideal(f*h*u*v*E+f*h*u+h*u*v+h*v*E+f,b*g*j*u*w+b*j*u*w+b*g*j+j*u*w+b,j*s*y+j*o+j*s+o,b*c*f*g+b*c*g*z+f*g*z+c*f+c*g,e*l*u*w+l*p,d*e*q*u+d*e*r*u+d*e*r+d*q*u+e+q,v*E,e*f*h*n+e*h*n*v+e*n*v,b*n*r+d*q*r+b*r,k*t*w*D+k*s*t+k*w*D,d*s*w+s*w*C+d*C,d*h*i*s*E+d*i*s+d*s*E+d*s,n*p*x*A+n*p*x+n,y,b*c*j*w+b*j*w+1,g*i*p*w+g*i+1,g*m*r*v+g*m*r+g*m*v+g*s+s*v+r,e*s*u*D+e*s*x+e*u+s,o,o*p*v*A+o*p*v+p*v+t*A+v,i*j*B+j*v*B,r*w*D+d*h+h*w+r*w+h*D,e*t*y+d*y,j*l*w*x*y,k*x*z+i*z*E+k*z*E+k*z+z*E,o*s*z*E+s,f*h*p*y+f*h*y+p*y,t*A,s*t+p*x+t*x+t,g*k*s*D+g*s*D+k*s*D+g*k+g*s+s)
--gbBoolean:      .112992 seconds.

--valence: 6
s11 = ideal(e*f*m*x*z*B+e*f*m*x*z+e*f*m*z*B+e*m*B+m*x*B,h*o*A+A*D,b*d*h*m*t+b*d*h*m+b*h*m*t+g*h*m*t+d*g*m+d*t+t,d*e*g*w+c*e*w+d*e*w+e*g*w+d*e*B+e*w*B+d*w,c*e*h*j*u*A+c*h*j*u+e*h*j*A+c*h*j+h*A+e+h,d*B*C*E+b*C,n*o*t*u+t*u*w*A+n*u*A,c*f*w*z+f*p*z+p*w*z,g*k*n*y*B+b*k*y+k*n*y+b*y*B+n*B,0,d*e*l*D*E+d*l*D*E+e*l*D*E+d*l*E+e*E,f*s*u*y+d*f*t+f*s*t,g*h*B*C+g*s*B*C+g*s*B+h*z+s*B,f*o*p*u*A*E+f*o*A*E+u*A+u,l*w*C+l*w*D+l*v+v*C+w,l*m*n*o*w+l*m*n*o*E+l*n*E,1,b*g*h*s*u+b*g*h*u+h*l*s*u+b*h*s+g*l*s+b*g*u,f*q*t+f*q+q*t,f*s*t*w*z+l*s*t*w+f*l*w*z+l*t*w*z,u,b*d*e*C+b*d*n+b*n*p+b*d*C,g*j*o*z*A+g*o*z*A+j*o,e*j*s*D+e*s*z*D+z*D,m*p*x*B+m*q,l*o*p*q*A+l*o*p*q*B+l*q*A+A*B+l,g*y*z*D+z*B*E+z+E,h*o*t*y*z+o*x+t*x,d*k*r*z+d*r*y*E+d*r*z+k*z*E+d*y+k*y+r,e*j*k*q+b*j*k+e*j*k+j*k*q+e)
--gbBoolean:      .000233 seconds.

--valence: 7
s12 = ideal(c*h*j*s*v+j*m*s*u*v+c*s*v+c*m+j*m,b*i*p*s*x*D+b*i*p*s*B*D+b*p*x+p*s*D+p*x*D,b*p*r*z+r*z*E,i*n*t*v*y,c*g*q+c*m*w+f*q,g*h*j*q*r*w+g*q,y,b*e*g*D+g*y*B*D,k*p*s*x*B*E,k*t*u*v*B*D+f*k*t*u*B+k*B+1,j*n*w*A,f*p*x+p*x+f,c*d*f*i*l+d*f*l*o+c*f*l*x+l*o*x,b*c*f*z*A+b*c,s*t*A*E+d*k*z+s*t+d,d*s*x*B*D+s*v*D,d*f*g*t*z+f*g*h*z+f,j*l*m*D+f*g*j,c*e*k*t*v+e*k*z*A+k*v*z*A,h*k*t*y*B+h*k*y*A+k*t*A+k*s*B,d*j*t,k*m*v*E+f*s*v*E+m*s*v*E+m*v*E+f*E,f*o*r+l,h*p*q*s*u*y+q*u*y+q*s+h*u,c*d*y*B+c*d*s*C,c*d*n*o*t,b*r*t*B*C+b*f*r*B+f*g+b*r,u*x*y*A,m*o*u*y*E+n*p*E,f*g*m*p*r+f*m*p*r*D+f*g*m*p+f*g*p*r+m*p)
-- gbBoolean:      .576008 seconds.

-- valence 8
s13 = ideal(d*C,b*e*m*w*z,b*j*l*s*w*x+j*l*q*s*x,k*l*m*n*v*w*B+k*m*n*w+k*l*w,d*h*s*t*u*A+d*e*h*s*t,c*e*k*n+i*k*o,c*j*o*z*D+c*o*x*z*D+c*z*B*D,m*s+e*u+s*x,m*p*s*x*y*z+e*m*x*y*z*D+p*s*y*z,f*i*k*r+f*i*r*E+r,b*i*o*z*C*E+b*i*z*C+b*i*C*E,f*j*s*v*x+e*j*v*E,e*i*k*p*B*E+e*k*p*C*E+i*k*p*C,f*o*u*x*E,b*e*m*v,b*l*n*t*u*B+b*d*h*l*u+b*h,h*j*n*p*s*B*E+s*t*B,g*l*o*z*C*D+g*l*o*C*D+i*C,d*n*o+n*z*C,h*n*p*x,f*j*n*s*D+j*s*w*C*D,b*c*h*q*u+b*c*q*u,e*k*B*C*E,b*d*i*m+i*m*w+s*w,c*e*k*r*t*B+k*m*r+e*m*z,t*u*z+j*x*z+m,d*q*C+u*B*C+l*q,c*e*m*D+g,e*l*o*q*s*z+d*e*o*s*u*z+l*q*u,i)
-- gbBoolean:      2.05947 seconds.

s14 = ideal(r*t,e*f*A*C,g*p*A*C,m*z*A,o*s,c*d*v*E,c*o,q*x,p*x*C,e*i*C,l*r,d*w,b*e*h,k*s*B,g*n*D,b*e*o*u,e*p*u,v*x,m*y*z,o*w*D,f*g*m*C,j*t,n*z*D*E,l*A,s*C,q*r*u,1,y*B*D,h*m*A*C,l*A)
-- gbBoolean:   .000655 seconds.

QR := makeRing(40,2);
TCR := ideal( x1 , x2 , x3 , x3*x8+x3 , x7+1 , x1*x2*x5+x1*x2 , x1*x4*x6+x1*x4+x1*x6 , x11 , x4*x6*x7+x4*x6+x7 , x6 , x6*x8*x9+x6*x9 , x11 , x12 , x11*x31 , x33 , x15 , x16 , x17 , x22 , x25*x26 , x37+1 , x23 , x24 , x27 , x24 , x39 , x28 , x29 , x30*x36 , x12 , x13 , x12 , x10*x11*x14*x31*x32+x10*x11*x31*x32+x11*x14*x31*x32 , x33 , x34 , x34*x35 , x38+1 , x35 , x40 , x35) 

QR = makeRing(12,2);
THBoolean = ideal( x9*x12+x9+x12 , x7*x11+x11 , 0 , x1*x10+x1 , x2*x10+x2 , x3*x8+x3 , x4 , x5 , x6*x11+x6 , x7*x12+x7+x12 , x8*x12+x8 , x7*x11*x12+x7*x11+x7*x12+x11*x12+x7+x12)

QR = makeRing(10,2);
Arapidopsis = ideal( 0 , x1 , 0 , x1*x5+x1+x5+1 , x2*x4*x6+x2*x4+x2*x6+x4*x6+x2+x4+x6+1 , 0 , 0 , x8*x9*x10+x8*x9 , x8*x9*x10+x8*x9 , 0)

booleanCellCycle = ideal( x1 , x1*x4*x5*x6*x10+x1*x4*x5*x6+x1*x4*x5*x10+x1*x4*x6*x10+x1*x5*x6*x10+x4*x5*x6*x10+x1*x4*x5+x1*x4*x6+x1*x5*x6+x4*x5*x6+x1*x4*x10+x1*x5*x10+x4*x5*x10+x4*x6*x10+x5*x6*x10+x1*x4+x1*x5+x4*x5+x4*x6+x5*x6+x1*x10+x4*x10+x5*x10+x1+x4+x5+x10+1 , x2*x5*x6*x10+x2*x5*x6+x2*x5*x10+x5*x6*x10+x2*x5+x5*x6+x2*x10+x5*x10+x2+x5+x10+1 , x2*x3+x3 , x2*x3*x5*x7*x8*x9+x2*x3*x5*x8*x9+x2*x3*x7*x8*x9+x2*x5*x7*x8*x9+x3*x5*x7*x8*x9+x2*x3*x5*x7+x2*x3*x8*x9+x2*x5*x8*x9+x3*x5*x8*x9+x3*x7*x8*x9+x5*x7*x8*x9+x2*x3*x5+x2*x3*x7+x2*x5*x7+x3*x5*x7+x3*x8*x9+x5*x8*x9+x2*x3+x2*x5+x3*x5+x3*x7+x5*x7+x3+x5 , x1*x4*x5*x10+x1*x4*x6*x10+x1*x5*x6*x10+x1*x4*x5+x1*x4*x6+x1*x5*x6+x1*x4*x10+x1*x5*x10+x4*x5*x10+x4*x6*x10+x5*x6*x10+x1*x4+x1*x5+x4*x5+x4*x6+x5*x6+x1*x10+x4*x10+x5*x10+x1+x4+x5+x10+1 , x10 , x5*x6*x7*x10+x5*x6*x7+x5*x6*x10+x5*x7*x10+x5*x6+x5*x7+x5*x10+x7*x10+x5+x10+1 , x5*x7*x8*x9*x10+x5*x7*x8*x9+x5*x8*x9*x10+x7*x8*x9*x10+x5*x8*x9+x7*x8*x9+x8*x9*x10+x8+1 , x7*x8+x7+x8+1 )

QR = makeRing(14,2);
drosophila = ideal( 0, x1*x4*x5*x6*x9+x1*x4*x5*x6+x1*x4*x5*x9+x1*x4*x6*x9+x1*x5*x6*x9+x4*x5*x6*x9+x1*x4*x5+x1*x5*x6+x4*x5*x6+x1*x4*x9+x1*x5*x9+x4*x5*x9+x1*x6*x9+x4*x6*x9+x5*x6*x9+x1*x4+x1*x5+x4*x5+x5*x6+x1*x9+x4*x9+x5*x9+x6*x9+x1+x4+x5+x9+1 , x2*x5*x6*x9+x2*x5*x6+x2*x5*x9+x2*x6*x9+x5*x6*x9+x2*x5+x5*x6+x2*x9+x5*x9+x6*x9+x2+x5+x9+1 , x2*x3*x13*x14+x3*x13*x14+x2*x3+x3 , x2*x3*x7*x8+x2*x3*x7+x2*x3*x8+x3*x7*x8+x2*x3+x3*x7+x3*x8+x3 , x1*x4*x5*x6+x1*x4*x5*x9+x1*x4*x6*x9+x1*x4*x5+x1*x4*x9+x1*x4+x5*x6+x5*x9+x6*x9+x5+x9+1 , x6*x9+x9 , x4*x5*x6*x9*x12+x4*x5*x6*x9+x4*x5*x6*x12+x4*x5*x9*x12+x4*x6*x9*x12+x4*x5*x6+x4*x5*x9+x4*x6*x9+x5*x6*x9+x4*x5*x12+x4*x9*x12+x4*x5+x5*x6+x4*x9+x5*x9+x6*x9+x4*x12+x4+x5+x9+1 , x7*x8*x10*x11+x7*x8*x10+x7*x10*x11+x8*x10*x11+x7*x8+x7*x10+x8*x10+x10*x11+x7+x8+x10+1 , x6*x9+x9+1 , x2*x3*x6*x9*x12+x2*x3*x6*x9+x2*x3*x9*x12+x3*x6*x9*x12+x2*x3*x9+x3*x6*x9+x2*x3*x12+x3*x9*x12+x6*x9*x12+x2*x3+x3*x9+x6*x9+x3*x12+x9*x12+x3+x9 , 0 , x4*x12+x12+1 , 0 )

QR = makeRing(20,2);
erbb2 = ideal( x13*x15*x18*x19*x20+x13*x15*x18*x19+x13*x15*x18*x20+x13*x15*x19*x20+x13*x18*x19*x20+x15*x18*x19*x20+x13*x15*x18+x13*x15*x19+x13*x18*x19+x15*x18*x19+x13*x15*x20+x13*x18*x20+x15*x18*x20+x13*x19*x20+x15*x19*x20+x18*x19*x20+x13*x15+x13*x18+x15*x18+x13*x19+x15*x19+x18*x19+x13*x20+x15*x20+x18*x20+x19*x20+x13+x15+x18+x19+x20 , x3*x4*x5+x3*x4+x4*x5+x4 , x2*x10*x12+x2*x10+x2*x12+x10*x12+x2+x10+x12+1 , x1*x9*x10*x12+x1*x9*x12+x9*x10*x12 , x2*x6*x10*x12+x2*x6*x10+x2*x6*x12+x2*x10*x12+x6*x10*x12+x2*x6+x2*x10+x6*x10+x2*x12+x6*x12+x10*x12+x2+x6+x10+x12+1 , x3*x5*x7+x3*x7+x5*x7+x7 , x12 , x2*x11 , x1*x10+x1+x10 , x13*x15*x18*x19*x20+x13*x15*x18*x19+x13*x15*x18*x20+x13*x15*x19*x20+x13*x18*x19*x20+x15*x18*x19*x20+x13*x15*x18+x13*x15*x19+x13*x18*x19+x15*x18*x19+x13*x15*x20+x13*x18*x20+x15*x18*x20+x13*x19*x20+x15*x19*x20+x18*x19*x20+x13*x15+x13*x18+x15*x18+x13*x19+x15*x19+x18*x19+x13*x20+x15*x20+x18*x20+x19*x20+x13+x15+x18+x19+x20 , x4 , x1*x9*x10+x1*x9+x1*x10+x9*x10+x1+x9+x10 , x9*x10*x18+x9*x10+x9*x18+x10*x18+x9+x10 , 1 , x14 , x14 , x14 , x16*x17 , x15*x16 , x15*x17) 


QR = makeRing(18,2);
yeastIron = ideal( x5+1 , x1*x2*x3*x6+x1*x2*x3+x1*x2*x6+x1*x3*x6+x2*x3*x6+x1*x2+x1*x3+x2*x3+x1*x6+x2*x6+x3*x6+x1+x2+x3 , x2 , x2*x8+x2 , x2 , x6*x7*x8*x13*x14*x16+x6*x7*x8*x13*x14+x6*x7*x8*x14*x16+x6*x7*x8*x14+x6*x7*x13*x16+x8*x13*x14*x16+x6*x7*x13+x6*x7*x16+x8*x14*x16+x6*x7+x13*x16+x16 , x6*x7*x8*x13*x14*x16+x6*x7*x8*x14*x16+x6*x7*x13*x16+x8*x13*x14*x16+x6*x7*x16+x8*x14*x16+x6*x7+x13*x16+x16 , x6*x7*x17 , x8 , x6*x9 , x9*x10 , x6*x7*x11+x6*x7+x7 , x3*x4*x6*x11*x12+x3*x4*x6*x12*x13+x3*x4*x6*x12+x3*x4*x11*x12+x3*x6*x11*x12+x4*x6*x11*x12+x3*x4*x6*x13+x3*x4*x12*x13+x3*x6*x12*x13+x4*x6*x12*x13+x3*x4*x12+x3*x6*x12+x4*x6*x12+x3*x11*x12+x4*x11*x12+x6*x11*x12+x3*x4*x13+x3*x6*x13+x4*x6*x13+x3*x12*x13+x4*x12*x13+x6*x12*x13+x3*x12+x4*x12+x6*x12+x3*x13+x4*x13+x6*x13+x12*x13+x12+x13 , x3*x4*x6*x11+x3*x4*x6+x3*x4*x11+x3*x6*x11+x4*x6*x11+x3*x4+x3*x6+x4*x6+x3*x11+x4*x11+x6*x11+x3+x4+x6+1 , x4*x6*x15*x18+x4*x6*x15+x4*x6*x18+x4*x15*x18+x6*x15*x18+x4*x6+x4*x15+x6*x15+x4*x18+x6*x18+x15*x18+x4+x6+x15 , x3*x4*x16*x18+x3*x4*x16+x3*x4*x18+x3*x16*x18+x4*x16*x18+x3*x4+x3*x16+x4*x16+x3*x18+x4*x18+x16*x18+x3+x4+x16 , x6*x15*x17*x18+x6*x15*x17+x6*x15*x18+x6*x15+x17*x18+x17 , x9*x11*x17*x18+x9*x11*x17 )


QR = makeRing(11,2);
yeastLi = ideal( 0 , x1*x2+x1*x10+x2*x10+x1+x2 , x1*x3+x1*x10+x3*x10+x1+x3 , x3 , x4*x5*x7*x8+x4*x5*x7*x10+x4*x5*x8*x10+x4*x7*x8*x10+x5*x7*x8*x10+x4*x5*x8+x4*x7*x8+x4*x5*x10+x4*x7*x10+x5*x8*x10+x7*x8*x10+x4*x5+x4*x7+x5*x7+x5*x8+x7*x8+x5*x10+x7*x10+x5+x7 , x7*x10+x7*x11+x10*x11+x7+x11 , x10*x11+x10+x11 , x2*x7*x8*x9+x2*x7*x9+x7*x8*x9+x2*x7+x2*x8+x7*x8+x2*x9+x8*x9+x2+x8 , x4*x6*x7*x8+x4*x6*x7*x9+x4*x6*x8*x9+x4*x7*x8*x9+x6*x7*x8*x9+x4*x6*x7*x10+x4*x6*x8*x10+x4*x7*x8*x10+x6*x7*x8*x10+x4*x6*x9*x10+x4*x7*x9*x10+x6*x7*x9*x10+x4*x8*x9*x10+x6*x8*x9*x10+x7*x8*x9*x10+x4*x6*x8+x4*x7*x8+x6*x7*x9+x4*x8*x9+x4*x6*x10+x4*x7*x10+x6*x8*x10+x7*x8*x10+x4*x9*x10+x8*x9*x10+x4*x6+x4*x7+x6*x7+x6*x8+x7*x8+x4*x9+x6*x9+x7*x9+x8*x9+x6*x10+x7*x10+x9*x10+x6+x7+x9 , x5*x7*x8*x9+x5*x7*x8*x10+x5*x7*x9*x10+x5*x8*x9*x10+x7*x8*x9*x10+x5*x7*x8*x11+x5*x7*x9*x11+x5*x8*x9*x11+x7*x8*x9*x11+x5*x7*x10*x11+x5*x8*x10*x11+x7*x8*x10*x11+x5*x9*x10*x11+x7*x9*x10*x11+x8*x9*x10*x11+x5*x7*x8+x5*x8*x9+x7*x8*x9+x5*x7*x10+x5*x9*x10+x7*x9*x10+x5*x7*x11+x5*x9*x11+x7*x9*x11+x8*x10*x11+x5*x8+x7*x8+x8*x9+x5*x10+x7*x10+x8*x10+x9*x10+x5*x11+x7*x11+x8*x11+x9*x11+x10*x11+x8+x10+x11 , x8*x10+x8+x10 )

--idealList = {II0, II0+II00, II1, II2, II3, II4, II5, II6}
--idealList = {II0, II0+II00, II2, II3, II4, II5, II6}
--idealList = {II3, II0+II00, II5, II6, II0, II4, II2}
idealList = {II3, II0+II00, II5, II0, II4, 
S1, S2, S3, S5,
s1, s2, s3, s4, s5,
s6, s7, s8, s9, s10, s11, s12, s13,
SS1, SS2, SS3, SS5,
shidokuNew
}
idealList = {TCR, THBoolean, Arapidopsis, booleanCellCycle, drosophila, erbb2, yeastIron, yeastLi}
--idealList = {shidokuNew}


end

ff := "outputtmpBio.txt";
counter := 0;
scan( idealList, i -> (
  counter = counter + 1;
  print ("Test number: " | counter);
  runBenchmark (i, ff)
) )
ff << endl << endl
ff << close;

end

restart
load "benchmarks.m2"

II3, II0+II00, II5, II0, II4, S1, S2, S3, S5, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, SS1, SS2, SS3, SS5, shidokuNew
II3  II0+II00  II5   II0   II4  S1   S2  S3  S5 s1   s2  s3  s4  s5 SS1  SS2
SS3  SS5  shidokuNew
II3, II0+II00, II5, II6, II0, II4, S1, S2, S3, S4, S5, SS1, SS2, SS3, SS4, SS5, shidokuNew


timing gens gb II3
timing gbBoolean II3

R = ZZ/2[ vars(1..36)]
QR = R / ideal apply(gens R, x -> x^2 + x)
ff := "outputtmp.txt";
--runBenchmark ideal makeBooleanNetwork(QR, 4, 10 )
ff <<  "Next computations in a quotient ring with " << numgens R << " variables." << endl;
ff <<  "valence: " << 5 << endl;
print ("valence: " | 5);
I := ideal makeBooleanNetwork(QR, 5, 10 );
print toString I
ff <<  I << endl;
runBenchmark (I,ff);
ff << endl << endl
ff << close;

load "benchmarks.m2"
n := 20
R = ZZ/2[ vars(1..n)]
QR = R / ideal apply(gens R, x -> x^2 + x)
ff := "outputtmp.txt";
--runBenchmark ideal makeBooleanNetwork(QR, 4, 10 )
apply( (1..5), i -> (
  ff <<  "Next computations in a quotient ring with " << numgens R << " variables." << endl;
  ff <<  "valence: " << i << endl;
  print ("valence: " | i );
  print;
  I := ideal makeBooleanNetwork(QR, i, 10 );
  print toString I;
  ff <<  I << endl; 
  ff << flush;
  runBenchmark (I,ff);
  ff << endl << endl
) ) 
ff << close;

end

runBenchmark J
runBenchmark (J+K)

runBenchmark ideal makeBooleanNetwork(QR, 14, 10 )
runBenchmark ideal makeBooleanNetwork(QR, 24, 10 )
runBenchmark ideal makeBooleanNetwork(QR, 36, 10 )
runBenchmark ideal makeBooleanNetwork(QR, 4, 10 )

end

load "benchmarks.m2"

-- gRevLex
restart
R = ZZ/2[w,x,y,z]
--R = ZZ/2[w,x,y,z, MonomialOrder=>Lex]
QR = R / ideal apply( gens R, x -> x^2 + x)
I = ideal (x+y)
I = ideal (x + y*z )
I = ideal () 

toString gens gb  ideal (x*y + w*z)

-- in gRevLex {{x*y+w*z, w*y*z+w*z, w*x*z+w*z}}
-- in Lex  {{x*y*z+x*y, w*z+x*y, w*x*y+x*y}}

testgb ideal (x*y + w*z)

a = toString (x*y+w*z,w*y*z+w*z,w*x*z+w*z)

testgb II3

restart
load "benchmarks.m2"
I = II0;
timing gbBoolean I

testgb II2
I = II0;
timing gbBoolean I

I = II2
testgb I

gbTrace = 1
timing ideal gens gb I
timing ideal gens gb II2
timing gbBoolean I


I = ideal (x + y*z )



I = ideal (x*y+z)



R = ZZ/5[x,y,z,w]
F = matrix(R, {{x+y, x, 3, y+5}})
G := F
sub( G,F)
sub( matrix {{0,1,1,0}},F)
sub( F, matrix {{0,1,1,0}})


 P
