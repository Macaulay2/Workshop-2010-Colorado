
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


