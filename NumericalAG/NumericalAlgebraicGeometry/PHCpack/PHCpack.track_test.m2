restart
loadPackage "NumericalAlgebraicGeometry"
-- debug NumericalAlgebraicGeometry; DBG = 1; printingPrecision = 20; 

R = CC[x,y];
S = {x*(x-1)*y,x*(x-1),(x-y)*(x+y+1)};
solsS = {{0,0},{1,1},{1,-1},{2,-2}}
T = {x*(x-1)*y,x*(x-1),y-(x+1)^2};
solveSystem(T,Software=>PHCpack)
print track(S,T,solsS, gamma=>0.6+0.8*ii,Software=>PHCpack)
refine(T,solsS,Software=>PHCpack,Iterations => 10, Bits => 400, ErrorTolerance => 1p400e-130)

 