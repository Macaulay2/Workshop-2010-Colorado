--With this Macaualy2 script we study the direct image complex of the versal
--deformation of vector bundles on PP^1 to its base space, following
--section 5 of the paper "Beilinson Monad and Direct Image for Families 
--of Coherent Sheaves" by David Eisenbud and Frank-Olaf
--Schreyer (posted on arXiv.org).
--This includes Example 5.2. 

--Begin executing the code after the first "end".

--Versal deformation of the direct sum of line bundles on P1
--For O(a1)+O(a2)+...+O(ad), 1<=a1<=...<=ad.
--

--Auxilliary functions called later in the file to define the
--versal deformation and its universal bundle:
sylvesterMatrix(ZZ,RingElement,RingElement):=(n,x,y)->(R:=ring x;
     matrix(apply(n+1,i->apply(n,j->if i==j then x else 
		    if i==j+1 then -y else 0_R))))

extensionMatrix=(a,b,LL)->(
     -- extension block with entries L
     matrix apply(a+1,i->apply(b,j->if i==0 and j<b-a-1 then LL_j else 0_S)))

setupDef=(L,kk)->(
-- input:
-- 	  L = list of twist 0 <L_0<=L_1<=...<=L_(k-1)
--        kk ground field     
-- creates:
--        the base ring A=kk[a's] for the versal deformation
--        O(L_0)+O(L_1)+...+O(L_(k-1)) on P^1,
--        the symmetric algebra S=A[x_0,x_1],
--        the extrerior E=A[e_0,e_1],
-- 	  xx=matrix{{x_0,x_1}}, ee=matrix{{e_0,e_1}}
-- output:
--        returns a presentation matrix of the versal deformation.
     k=#L;
     as:=toList join toSequence apply(k,i->join(
	       toSequence apply(i,j->apply(L_i-L_j-1,t->a_(j,i,t)))));
     degas:=toList join toSequence apply(k,i->join(
	       toSequence apply(i,j->L_i-L_j-1:{2*(i-j),0})));    
     A=kk[as,Degrees=>degas];
     degas1:=toList join(toSequence degas,(2:{1,1}));
     E=kk[join(as,{e_0,e_1}),Degrees=>degas1,SkewCommutative=>{#as,#as+1}];
     S=kk[join(as,{x_0,x_1}),Degrees=>degas1];
     ee=matrix{{e_0,e_1}};
     xx=matrix{{x_0,x_1}};
     M:=sylvesterMatrix(L_0,x_0,x_1);
     use S;LL={};NN:=matrix{{0_S}};
     apply(1..#L-1,i->(LL=toList apply(L_i-L_0-1,t->x_1*a_(0,i,t));
	 M=M|extensionMatrix(L_0,L_i,LL)));
     apply(1..#L-1,j->(
	       NN=map(S^(L_j+1), S^(sum(0..j-1,t->L_t)),0);
	       NN=NN|sylvesterMatrix(L_j,x_0,x_1);
	       apply(j+1..#L-1,i->(LL=toList apply(L_i-L_j-1,t->x_1*a_(j,i,t));
	NN=NN|extensionMatrix(L_j,L_i,LL)));
     	M=M||NN));
        da:=toList join toSequence apply(k,i->L_i+1:{-2*i,0}); 
     	db:=toList join toSequence apply(k,i->L_i:{-2*i-1,-1});
	map(S^da,S^db,M)
	)
end 


----- Example 5.2: the special case O(6,0,0)
restart
load "computingRpi_star.m2"
load "vectorBundlesOnPP1.m2"
--Although we treat the bundle of type 6,0,0 in our paper, the code 
--requires that we shift every summand to be strictly positive and work
-- with the bundles in increasing order: thus here we treat 1,1,7. 
--The same is true for all examples treated below.
L={1,1,7} -- splitting type
kk=ZZ/101 -- ground field we will use
M=setupDef(L,kk) -- Defines the ring of the 
--versal deformation, and sets M so that coker M is the universal bundle
N=symmetricToExteriorOverA(M,ee,xx) -- moves to the exterior algebra;
--ker N is the module corresponding to the linear free resolution of
--a truncation of coker M
fN=res(coker N,LengthLimit=>7)
bettiT dual fN -- the betti table as defined in the paper
--   index: -7 -6 -5 -4 -3 -2 -1 0
--      -2: 15 12 10  8  6  4  2 .
--      -1:  .  1  2  3  4  5  6 9
Rpis1=apply(-6..-2,i-> degreeZeroPart(fN[-i]**E^{{0,-i+1}},A))
--the sequence of the "non-trivial" direct image complexes for various
--twists of the universal bundle.

Bs1=apply(Rpis1,c->c.dd_0)
-- the list of the matrices representing the differentials of the direct image complexes
-- Now we change to the variable names used in the paper
B=kk[a_0..a_4,b_0..b_4]
Bs=apply(Bs1,m->substitute(m,vars B))
J=apply(2..4,i->ideal mingens minors(i,Bs#3));
--ideals of minors of the square matrix
-- Conjecture 5.1 asserts that all these ideals of minors are radical
apply(J,j->(dim j,codim j, degree j,betti res j))
-- numerical information of these ideals
betti J#1
-- We next show that J#1 is not a prime ideal and construct a decomposition:
J1b=J#1:minors(2,Bs#4);
betti res J1b
minors(3,Bs#2)==J1b 
intersect(minors(3,Bs#2),minors(2,Bs#4))==minors(3,Bs#3)

Bs#1 
--This is a 1-generic 2x2 matrix, whose 2x2 minors are the defining
--ideal of a rational normal scroll, and thus are prime.
-- The ideals of 2x2 minors of Bs#3 and Bs#2
-- are equal to these, thus also prime
minors(2,Bs#3)==minors(2,Bs#2)
minors(2,Bs#3)==minors(2,Bs#1)

-- According to Conjecture 5.1 the strata in the stratification by splitting type 
-- have defining ideals equal to the following ideals:
-- Splitting type 4,2,0:
betti res (J420=ideal mingens (minors(3,Bs#2)+minors(2,Bs#4)))
degree J420
--strata of the other splitting types:
J510=minors(2,Bs#1);
J411=minors(3,Bs#2);
J330=minors(2,Bs#4);
J321=minors(4,Bs#3);
strata={J321,J330,J411,minors(3,Bs#3),J420,J510};
--and their numerical information:
apply(strata,s->print(dim s, codim s, degree s, betti res s ));


-- We show that J411 is actually the 
--defining ideal of the secant locus Sec(S(4,4)); in particular it is prime.
-- First paramtrize the secant locus to find its prime ideal
R=kk[u_0..u_2,v_0..v_2,s_0..s_2,t_0..t_2]
uu=matrix{apply(5,i->sum(2,j->s_j^i*t_j^(4-i)*u_j))}
vv=matrix{apply(5,i->sum(2,j->s_j^i*t_j^(4-i)*v_j))}
phi=map(R,B,uu|vv)
--and compute the prime ideal:
betti(Jo=ker phi)
--Check that it's the same:
Jo==J411
-- This implies that Sec(S(4,4)=minors(3,B_{3,3})

--Same for other secant loci
-- identify Sec^3 S(4,4)
-- uu=matrix{apply(5,i->sum(3,j->s_j^i*t_j^(4-i)*u_j))}
-- vv=matrix{apply(5,i->sum(3,j->s_j^i*t_j^(4-i)*v_j))}

--phi=map(R,B,uu|vv)
--time J1=ker phi --Takes some time!


-----    Further examples  ----------------------------

------------------- Splitting type 7,0,0
restart
load "computingRpi_star.m2"
load "vectorBundlesOnPP1.m2"
-- this example is interesting because in this case an ideal of minors
-- has components of different dimensions, inparticular it is not Cohen-Macaulay
L={1,1,8}
kk=ZZ/101
M=setupDef(L,kk)
N=symmetricToExteriorOverA(M,ee,xx)
fN=res(coker N,LengthLimit=>7)
bettiT dual fN
--index: -7 -6 -5 -4 -3 -2 -1  0
--       -2: 14 12 10  8  6  4  2  .
--       -1:  1  2  3  4  5  6  7 10
Rpis1=apply(-8..-2,i-> degreeZeroPart(fN[-i]**E^{{0,-i+1}},A))
A=kk[a_0..a_5,b_0..b_5]
Bs1=apply(Rpis1,c->substitute(c.dd_0,vars A))

minors(3,Bs1#5)==intersect(minors(2,Bs1#6),minors(3,Bs1#4))
dim minors(3,Bs1#4)+1==dim minors(2,Bs1#6)
-- => ideal of minors(3,Bs1#5) has components of differerent dimensions
apply({minors(3,Bs1#5),minors(2,Bs1#6),minors(3,Bs1#4),minors(2,Bs1#6)+minors(3,Bs1#4)},c->(dim c,degree c))
---------------------------------------------


------------------- 8,0,0,0
restart
load "computingRpi_star.m2"
load "vectorBundlesOnPP1.m2"
-- another example where we work out the dimensions of the various strata
L={1,1,1,9}
kk=ZZ/101
M=setupDef(L,kk)
time N=symmetricToExteriorOverA(M,ee,xx);
time fN=res(coker N,LengthLimit=>8)
bettiT dual fN
--    index: -8 -7 -6 -5 -4 -3 -2 -1  0
--       -2: 24 21 18 15 12  9  6  3  .
--       -1:  1  2  3  4  5  6  7  8 12
Rpis1=apply(-9..-2,i-> degreeZeroPart(fN[-i]**E^{{0,-i+1}},A))
R=kk[x_0..x_6,y_0..y_6,z_0..z_6]
Bs=apply(Rpis1,c->substitute(c.dd_0,vars R))
strata={
J3221=minors(6,Bs#6),
J3311=minors(5,Bs#6),
J4211=minors(5,Bs#5),
J3320=minors(3,Bs#7),
J4220=minors(5,Bs#5)+minors(3,Bs#7),
J4310=minors(5,Bs#5)+minors(4,Bs#6)+minors(3,Bs#7),
J5111=minors(4,Bs#4),
J5210=minors(4,Bs#4)+minors(3,Bs#7),
J4400=minors(2,Bs#7),
J6110=minors(3,Bs#3)+minors(3,Bs#7),
J5300=minors(4,Bs#4)+minors(2,Bs#7),
J6200=minors(3,Bs#3)+minors(2,Bs#7),
J7100=minors(2,Bs#2),
J8000=minors(1,Bs#1)};
time apply(strata,c->(dim c, degree c))
minors(4,Bs#5)==intersect(J4400,J5111)
minors(3,Bs#6)==intersect(J6110,J4400)
time minors(4,Bs#6)==intersect(J5111,J4310)
apply(strata,c->(codim c, betti mingens c))
         codim J8000==21
	 codim J7100==17
	 codim J6200==15
codim J6110==13 and codim J5300==13              
       codim J5210==10 and codim J4400==12
codim J5111==9 and codim J4310==8
                   codim J4220==7
codim J4211==5 and codim J3320==5
         codim J3311==4
         codim J3221==1
	 
------------------------------------------

