
restart

loadPackage "BenchmarkGb"


-- Computations for Shidoku with Boolean polynomials.  J are the shidoku polynomials and K is a set of initial clues to give a unique answer.

S = ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder=>Lex]
II0 = ideal {a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
II00 = ideal {d1, d2, d3, d4-1, e1, e2, e3, e4-1, g1, g2-1, g3, g4, j1, j2, j3-1, j4, l1-1, l2, l3, l4, m1-1, m2, m3, m4}

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


--idealList = {II0, II0+II00, II1, II2, II3, II4, II5, II6}
--idealList = {II0, II0+II00, II2, II3, II4, II5, II6}
idealList = {II3, II0+II00, II5, II6, II0, II4, II2}
--idealList = { II3, II4, II5, II6}
ff := "outputtmp.txt";
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
