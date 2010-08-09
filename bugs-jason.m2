R = ZZ/32003[u,v,w,x,y,z]  
--with default monomial ordering
I = ideal(w^4,x^4,w^2*y^2+x^2*z^2 + w*x*(y*u + z*v))
G = gb(I,Algorithm=>LinearAlgebra)
gens G
regularity I
--Unknown engine error
betti res I
--Although this seems to work and shows reg = 9