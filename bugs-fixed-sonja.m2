-- the function toBinomial in the package FourTiTwo had a bug:

-- it was converting a vector [1,0,0] into a corresponding "binomial" x-1 
-- in the ring QQ[x,y,z] 

-- and now it converts it to x, as it should. 

-- this package should be updated. the new file FourTiTwo.m2 is in the repository.

loadPackage "FourTiTwo"
b=matrix"1,0,0"
toBinomial(b,QQ[x,y,z])