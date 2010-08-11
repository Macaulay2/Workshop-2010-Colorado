restart
kk=ZZ/101
A = kk[t]
S = A[x,y]
I = module ideal (x^2, y^4, t^2,t)
truncate ({4,0},I) -- sometimes no error msg the first time! -- and a correct answer.
truncate ({4,0},I)
