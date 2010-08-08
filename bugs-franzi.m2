
-- lex order takes longer than several minutes (it never finished for me) 
-- computing a basis first in gRevLex order, lifting in Lex order, and recomputing a basis is quick
restart
R=QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]
--R=QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p, MonomialOrder=>Lex]
K1 = {(a-1)*(a-2)*(a-3)*(a-4), (b-1)*(b-2)*(b-3)*(b-4),(c-1)*(c-2)*(c-3)*(c-4), (d-1)*(d-2)*(d-3)*(d-4),(e-1)*(e-2)*(e-3)*(e-4), (f-1)*(f-2)*(f-3)*(f-4),(g-1)*(g-2)*(g-3)*(g-4), (h-1)*(h-2)*(h-3)*(h-4),(i-1)*(i-2)*(i-3)*(i-4), (j-1)*(j-2)*(j-3)*(j-4),(k-1)*(k-2)*(k-3)*(k-4), (l-1)*(l-2)*(l-3)*(l-4),(m-1)*(m-2)*(m-3)*(m-4), (n-1)*(n-2)*(n-3)*(n-4),(o-1)*(o-2)*(o-3)*(o-4), (o-1)*(o-2)*(o-3)*(o-4), a+b+c+d-10,a*b*c*d-24, e+f+g+h-10, e*f*g*h-24, i+j+k+l-10, i*j*k*l-24,m+n+o+p-10, m*n*o*p-24, a+e+i+m-10, a*e*i*m-24, b+f+j+n-10,b*f*j*n-24, c+g+k+o-10, c*g*k*o-24, d+h+l+p-10, d*h*l*p-24,a+b+e+f-10, a*b*e*f-24, c+d+g+h-10, c*d*g*h-24, i+j+m+n-10,i*j*m*n-24, k+l+o+p-10, k*l*o*p-24}
K2 = {d-4, e-4, g-2, j-3, l-1, m-1}
J=ideal(K1)
K=ideal(K2)
timing gens gb(J+K) --0.002367 seconds
--timing G = gens gb(J, Algorithm=>Sugarless)  --5.89729 seconds
timing G = gens gb(J)  --6.89729 seconds
RLex=QQ[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p, MonomialOrder=>Lex]
Glex = sub(G, RLex)
timing gens gb Glex -- .567208 seconds
