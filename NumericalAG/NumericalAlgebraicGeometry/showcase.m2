needsPackage "NumericalAlgebraicGeometry"
NAGtrace 2
load "benchmarks.m2"

-- BENCHMARK SYSTEMS: ---------------------------------------------------------
systems = {
     -- random system in n variables of degree d 
     (n = 5; d = 4; setRandomSeed 0; -- #sols=1024, M2:4, H:11, B:51, P:63
	  T = (randomSystem(n,d,CC))_*; (S,solsS) = totalDegreeStartSystem T; (T,S,solsS)), 
     (n = 5; d = 5; setRandomSeed 0; -- #sols=3125, M2:30, H:78, B:402, P:550
	  T = (randomSystem(n,d,CC))_*; (S,solsS) = totalDegreeStartSystem T; (T,S,solsS)), 
     -- katsura
     (T = (katsuraBench 11)_*; -- #sols=1024, M2:4, H:7, B:15, P:37
	  (S,solsS) = totalDegreeStartSystem T; (T,S,solsS)), 
     (T = (katsuraBench 12)_*, -- #sols=2048, M2:11, H:19, B:37, P:102
	  (S,solsS) = totalDegreeStartSystem T; (T,S,solsS)), 
     -- random generalized eigenvalue problem
     (setRandomSeed 0; randomGeneralizedEigenvalueProblem 35) -- #sols=35, M2:3, B:40, P:323 
     };
softwares = {M2engine,Bertini,PHCpack,HOM4PS2};

for system in systems do (
     (T,S,solsS) = system;
     sols = new HashTable from apply(softwares, soft->(
	       << "---------------------------------------------------------" << endl;
	       << "---------- COMPUTING with " << soft << "-----------------" << endl; 
	       << "---------------------------------------------------------" << endl;
	       soft=>sortSolutions if soft===HOM4PS2 then solveSystem(T,Software=>soft)
	       else 
	       track(S,T,solsS,gamma=>1+ii,Software=>soft)
	       ));
     --assert all(drop(softwares,1), soft->areEqual(sols#soft/(s->{first s}),sols#(first softwares),Tolerance=>1e-3));
     --on large problems some of the softwares do not refine solutions to high enough precision -- can't check the match
     )
 
end
restart
load "showcase.m2"
M = sols#(first softwares);
<< "Multiple solutions: " << select(toList(0..#M-2), i->areEqual(first M#i,first M#(i+1),Tolerance=>1e-3)) << endl;
assert all(#M, i->getSolution(i,SolutionAttributes=>SolutionStatus)=="REGULAR") 
<< "Large residual: " << select(toList(0..#M-2), i->norm sub(matrix {T}, matrix M#i)>0.001) << endl;

-- try projective tracker
(T = (katsuraBench 11)_*;
     (S,solsS) = totalDegreeStartSystem T;
     (T,S,solsS));
predictor=RungeKutta4;    
predictor=Tangent;    
S1 = track(S,T,solsS,gamma=>0.6+0.8*ii,Predictor=>predictor);
sum(#S1,i->getSolution(i,SolutionAttributes=>NumberOfSteps))//#S1
S2 = track(S,T,solsS,gamma=>0.6+0.8*ii,Projectivize=>true,Normalize=>true,Predictor=>predictor);
sum(#S2,i->getSolution(i,SolutionAttributes=>NumberOfSteps))//#S2
areEqual(sortSolutions S1, sortSolutions S2)
