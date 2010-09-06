newPackage(
	"QuillenSuslin",
    	Version => "0.1", 
    	Date => "August 08, 2010",
    	Authors => {
	     {Name => "Hirotachi Abo", Email => "abo@uidaho.edu", HomePage => "http://www.webpages.uidaho.edu/~abo/"},
	     {Name => "Brett Barwick", Email => "barwicjb@mailbox.sc.edu", HomePage => "http://www.math.sc.edu/~barwicjb/"},
	     {Name => "Branden Stone", Email => "", HomePage => ""}	     
	     },
    	Headline => "QuillenSuslin",
    	DebuggingMode => true
    	)

export {
     "computeFreeBasis",
     "applyRowShortcut",
     "maxMinors",
     "isProjective",
     "isUnimodular",
     "qsAlgorithmPID",
     "qsAlgorithm",
     "qsAlgorithmRow",
     "findMaxIdeal",
     "changeVar",
     "suslinLemma",
     "leadCoeffVar",
     "degVar",
     "horrocks",
     "patch",
     "commonDenom"
}

------------------------------------------------------------
-- Small helper methods
------------------------------------------------------------

-- Compute the ideal of maximal minors of a matrix.

maxMinors = method()
maxMinors(Matrix) := M -> (
     local R; local i; 
     R = ring(M);
     i = min({rank target M, rank source M});
     while minors(i,M) == 0 and i > 0 do i=i-1;
     return minors(i,M);
)


-- Compute the minor of a matrix obtained by crossing
-- out the ith column or ith row.

colMinor = method()
colMinor(Matrix,ZZ) := (M,i) -> (
     return det(submatrix'(M,,{i}));
)

rowMinor = method()
rowMinor(Matrix,ZZ) := (M,i) -> (
     return det(submatrix'(M,{i},));
)


-- Input: A module P over a Noetherian ring R.
-- Output: 'true' if P is projective, 'false' if P is not projective.

isProjective = method()
isProjective(Module) := P -> (
     local R;
     R = ring(P);
     return isUnimodular(presentation(P))
)


-- Checks whether a given matrix is unimodular.  (ie. its maximal minors generate the unit ideal.)

isUnimodular = method()
isUnimodular(Matrix) := M -> (
     local R;
     R = ring(M);
     if maxMinors(M) == R then return true else return false;
)


-- Returns the leading coefficient of a multivariate
-- polynomial with respect to a particular variable.

leadCoeffVar = method()
leadCoeffVar(RingElement,RingElement) := (f,var) -> (
     return (flatten coefficients(f,Variables =>{var}))#1_(0,0); 
)     
     

-- Returns the degree of a multivariate polynomial
-- with respect to a particular variable.

degVar = method()
degVar(RingElement,RingElement) := (f,var) -> (
     return rank source((flatten coefficients(f,Variables =>{var}))#0) - 1;
)


-- Finds the least common denominator of all entries of a matrix
-- over a fraction field by finding the LCM of all denominators.

commonDenom = method()
commonDenom(Matrix) := M -> (
     nCol = rank source M;
     nRow = rank target M;    
     denomList = new List from {};
     apply(0..(nRow - 1), i -> (apply(0..(nCol - 1), j -> (denomList = append(denomList,denominator(M_(i,j)))))));
     return lcm(denomList);
) 

------------------------------------------------------------
------------------------------------------------------------

------------------------------------------------------------
-- Core methods in the QuillenSuslin package
------------------------------------------------------------

-- Core program to compute the free basis
-- Needs QSAlgorithm

computeFreeBasis = method()
computeFreeBasis(Matrix) := Matrix => phi -> (
     R := ring phi;
     fphi := res coker phi;
     p := length fphi;
     Ai := fphi.dd_p;
     for i from 0 to p-2 do (
	  tAi := transpose Ai;
	  idi := map(target tAi,target tAi,1_R);
	  Bi := transpose (idi // tAi);
	  Ui := QSAlgorithm(Bi);
	  nrowi := rank target Bi;
	  nrowi' := rank target Ui;
	  ncoli := nrowi'-nrowi;
	  Vi := submatrix(Ui,{0..nrowi'-1},{nrowi..nrowi'-1});
	  Ci := fphi.dd_(p-i-1)*Vi;
	  Ai = Ci;
     );
     Ai
)


-- Shortcuts from Fabianska's PhD thesis.
-- There is a problem with shortcut 2.2.1(2).
-- To see this, run the following commands:
-- R = QQ[x,y]
-- f = matrix{{x^2+1,x-2,x^2+3,x-3}}
-- U = applyRowShortcut(f)

applyRowShortcut = method()
applyRowShortcut(Matrix) := g -> (
     local R; local f; local n; local s; local M1; local M2; local M3; local M4; local U1; local U2; local U3; local U4; local U5;
     R = ring g;
     f = flatten entries g;
     n = #f;
     
     -- Fabianska shortcut 2.2.1(1).
     s = scan( n, i -> ( if ideal f_i == R then break i ) );
     
     if s =!= null
     then (
	  print("Using shortcut 2.2.1(1).");
	  -- Swap g1 and gs.
	  M1 = mutableIdentity(R,n);
	  M1_(0,0) = 0;
	  M1_(s,s) = 0;
	  M1_(0,s) = 1;
	  M1_(s,0) = 1;
	  gSwap = g*matrix(M1);
	  S = map(R^1) // matrix{{gSwap_(0,0)}};
	  M2 = mutableIdentity(R,n);
	  M2_(0,0) = S_(0,0);
	  apply(1..(n-1), i -> (M2_(0,i) = -S_(0,0)*gSwap_(0,i)));
	  U1 = matrix(M1)*matrix(M2);
	  return matrix U1;
	  );
     
     -- Fabianska shortcut 2.2.1(2).
     S = subsets(f,2);
     h = scan ( #S, i -> ( 
	       if ideal S_i == R 
	       then break S_i;
	       )
	  );
     if h =!= null
     then (
	  print("Using shortcut 2.2.1(2).");
	  ss = position( f, i -> ( i == h_0 ) );
	  t = position( f, i -> ( i == h_1 ) );
	  	  
	  H = 1_R//gens ideal h;
	  W = mutableIdentity(R,n);
	  W_(ss,0) = H_(0,0);
	  W_(t,0) = H_(1,0);
	  W_(ss,1) = -h_1;
	  W_(t,1) = h_0;
	  if ( ss>1 or t>1 )
	  then (
	       r = first rsort {ss,t};
	       W_(1,1) = 0;
	       W_(1,r) = 1;
	       W_(r,r) = 0;
	       );
	  G = delete( h_1, delete( h_0, f ) );
	  V = mutableIdentity(R,n);
	  scan(2..(n-1), i -> ( V_(0,i) = -G_(i-2) ) );
	  U2 = matrix W*matrix V;
	  return U2;
     );
    
     -- Fabianska shortcut 2.2.1(3).
     s = scan(n, i -> (if ideal submatrix(g,,{i}) == R then break i));
     if s =!= null then (
	  print("Using shortcut 2.2.1(3).");
	  M1 = mutableIdentity(R,n);
	  M1_(0,0) = 0;
	  M1_(s,s) = 0;
	  M1_(0,s) = 1;
	  M1_(s,0) = 1;
          gSwap = g*matrix(M1);
	  -- Now gSwap_(0,1) = 0.
	  h = map(R^1) // submatrix'(gSwap,,{0});
	  M2 = mutableIdentity(R,n);
	  apply(1..(n-1), i -> (M2_(i,0) = (1-gSwap_(0,0))*h_(i-1,0)));
	  M3 = mutableIdentity(R,n);
	  apply(1..(n-1), i -> (M3_(0,i) = -gSwap_(0,i)));
	  U3 = matrix(M1)*matrix(M2)*matrix(M3);
	  return U3;
     );

     -- Fabianska shortcut 2.2.2(1).
     l := flatten entries (map(R^1) // g);
     w := scan( n, i -> ( if ideal l_i == R then break i ) );
     if w =!= null
     then (
	  print("Using shortcut 2.2.2(1).");
	  scan( n, i -> ( U4_(i,w) = l_i ) );
	  M1 = mutableIdentity(R,n);
	  M1_(0,0) = 0;
	  M1_(w,w) = 0;
	  M1_(w,0) = 1;
	  M1_(0,w) = 1;
	  M2 = mutableIdentity(R,n);
	  apply(1..(n-1), i -> (M2_(0,i) = -(g*matrix(M1))_(0,i)));
	  U4 = matrix(M1)*matrix(M2);
	  return matrix U4;
	  );
     
     -- Fabianska shortcut 2.2.2(2).
     S = subsets(l,2);
     s = scan(n, i -> (if ideal S_i == R then break S_i;));
     if s =!= null then (
	  print("Using shortcut 2.2.2(2).");
	  p1 = position(l, i -> (i == s_0));
	  p2 = position(l, i -> (i == s_1));
	  M1 = map(R^1) // gens ideal s;
	  M2 = mutableIdentity(R,n);
     -- Swap so that the first two elements of l generate R.
	  M2_(0,0) = 0;
	  M2_(p1,p1) = 0;
	  M2_(1,1) = 0;
	  M2_(p2,p2) = 0;	  
	  M2_(0,p1) = 1;
	  M2_(p1,0) = 1;
	  M2_(1,p2) = 1;
	  M2_(p2,1) = 1;
	  M3 = mutableIdentity(R,n);
	  lSwap = matrix{l}*matrix(M2);
	  gSwap = g*matrix(M2);
	  apply(0..(n-1), i -> (M3_(i,0) = lSwap_(0,i)));
	  M3_(0,1) = -M1_(1,0);
	  M3_(1,1) = M1_(0,0);
	  print(matrix M3);
	  M4 = mutableIdentity(R,n);
	  M4_(0,1) = -(-M1_(1,0)*gSwap_(0,0)+M1_(0,0)*gSwap_(0,1));
	  apply(2..(n-1), i -> (M4_(0,i) = -(gSwap)_(0,i)));
	  print(matrix M4);
	  U5 = matrix(M2)*matrix(M3)*matrix(M4);
	  return U5;  	  
     );
)


-- This method takes a unimodular matrix phi over a PID and returns a unimodular matrix U such that phi*U = (I | 0).
-- This works as long as Macaulay2 computes the Smith normal form like I think it does.

qsAlgorithmPID = method()
qsAlgorithmPID(Matrix) := Matrix => phi -> (
     local D; local F; local G; local H1; local H2; local U';
     (D,F,G) = smithNormalForm(phi);
     H1 = submatrix(G,[0..(rank source phi - 1)],[0..(rank target phi - 1)]);
     H2 = submatrix(G,[0..(rank source phi - 1)],[(rank target phi)..(rank source phi - 1)]);
     U' = H1*F | H2;
     V = submatrix(phi*U',[0..rank target phi-1],[0..rank target phi-1]);
     B = prune image(V);
     C = gens B // V;
     U = U'*(C ++ map(R^(rank source phi - rank target phi)));
     return U; 
)

-- For a given unimodular matrix U, qsAlgorithm computes a matrix N such that 
-- U*N is the matrix of the form (I | 0).
-- Still need to implement qsAlgorithmRow.

qsAlgorithm = method() 
qsAlgorithm(Matrix) := Matrix => phi -> (
     R := ring phi;
     nrow := rank target phi;
     ncol := rank source phi;
     r := ncol - nrow;
     -- Implements the shortcut for (p-1) x p unimodular
     -- matrices from Fabianska section 2.2.1.
     
     -- Better to invert and calculate row minors
     -- or calculate column minors and then factor map?
     -- Both of the following work and seem to be fast.
     -- Make decision after trying more computationally
     -- intensive examples.
     
     -- Compute column minors and factor map:
     if r == 1 then (
	  M = mutableMatrix(R,1,ncol);
	  for i from 0 to ncol-1 do M_(0,i) = colMinor(phi,i);
	  M = matrix M;
	  N = map(R^1) // M;
	  bottomRow = mutableMatrix(R,1,ncol);
	  for i from 0 to ncol-1 do bottomRow_(0,i) = (-1)^(ncol+1+i)*N_(i,0);
	  bottomRow = matrix bottomRow;
	  return inverse(phi || bottomRow);
	  );
     
     -- Invert and calculate row minors:
     {*if r == 1 then (
	  M = inverse(phi);
	  bottomRow = mutableMatrix(R,1,ncol);
	  for i from 0 to ncol-1 do bottomRow_(0,i) = (-1)^(ncol+1+i)*rowMinor(M,i);
	  bottomRow = matrix bottomRow;
	  print("Used shortcut 2.2.1 2");
	  return inverse(phi || bottomRow);
	  );
     *}
      
     Ai := phi;
     ai := Ai^{0};
     Ui := qsAlgorithmRow(ai);
     Ai = Ai*Ui;
     for i from 1 to nrow-1 do (
	  Bi := submatrix(Ai,{i..nrow-1},{i..ncol-1});
	  bi := Bi^{0};
	  Ui' := qsAlgorithmRow(bi);
	  idi := map(R^i);
	  Ui'' := idi++Ui';
	  Ui = Ui*Ui'';
	  Ai = Ai*Ui'';
	  );
     Vi := prune image Ai;
     V := (gens Vi // map(R^nrow,R^ncol,Ai))|(map(R^(nrow-r),R^r,0_R)||map(R^r));
     Ui*V
     )

-- Finds a maximal ideal containing a given ideal.
-- Only works over QQ.
-- Quick and dirty method thanks to Jason.

findMaxIdeal = method()
findMaxIdeal(Ideal) := (I) -> (
     local R;
     R = ring(I);
     m := I;
     h := codim I;
     d := dim R;
     while h < d do(
	  L = minimalPrimes m;
	  ok = false;
	  while not ok do(
	       f = random(1,R);
	       ok = all(L, p->f % p != 0);
	       );
	  m = m + ideal(f);
	  h = codim m;
	  print h;
	  );
     m
)

-- Changes variables according with Noether's theorem (Lemma 2.3.1, Fabianska)
-- Outputs: (1) new unimodular row with leading term of first entry a pure power
-- of the "last" variable. (2) a function to reverse the change of variable.

changeVar = method()
changeVar( Matrix, RingElement ) := (M,x) -> (
     f := first flatten entries M;
     m := first degree f + 1;

     R := ring f;
     var := flatten entries vars R;
     s := position( var, i -> ( i == x ) ); -- Very much depends on the way the user inputs the variables 
     varTail := drop( var, s );
     y := apply( s+1 , i -> ( var_i ) );
               
     y = toList apply( 0..(s-1) , i -> ( y_i - x^(m^(s-i)) ) );
     y = y|varTail;
     N1 := sub( M , matrix{ y } );
     y = toList apply( 0..(s-1) , i -> ( var_i + x^(m^(s-i)) ) );
     y = y|varTail;
     print y;
     phi := (map(ring matrix{ y },ring M,matrix{ y }));
     (N1,phi)
)


-- Effective version of Suslin's Lemma which takes two
-- polynomials with deg(f) = s and deg(g) <= s-1, f monic,
-- and one of the coefficients of g a unit, and produces
-- a polynomial h in (f,g) with deg(h) = deg(g) and the
-- leading coefficient of h is a unit in R_I. 

suslinLemma = method()
suslinLemma(RingElement,RingElement,RingElement,Ideal) := (f,g,var,I) -> (
     lcf = leadCoeffVar(f,var);
     lcg = leadCoeffVar(g,var);
     while lcg % I == 0 do (
	  g = lcf*var^(degVar(f,var)-degVar(f,var))*g - lcg*f;
	  lcg = leadCoeffVar(g,var);
     );
     return g;
)


-- Effective version of Horrock's Theorem which takes
-- a unimodular row f over R[x1,...,xn-1][currVar] where the
-- first component is monic in currVar and computes
-- a local solution to the unimodular row problem when we
-- localize at the given maximal ideal.

-- Output: U, where U is a matrix which transforms f
-- to the form (1 0 ... 0) and is unimodular over the localization.

horrocks = method()
horrocks(Matrix,RingElement,Ideal) := (f,currVar,I) -> (
     
     R = ring f;
     
     -- Throw errors if f does not meet requirements.
     
     if leadCoeffVar(f_(0,0),currVar) != 1_R then (
	  print("Error: The first element of the row is not monic in the given variable.");
	  return (null,null);
     );

     if isUnimodular(f) == false then (
	  print("Error: The given row is not unimodular.");
	  return(null,null);
     );

     nCol = rank source f;
     U = map(R^nCol);
          
     -- Take care of a few special cases first.
     
     -- These should already be covered in applyRowShortcut
     -- but should be available here if horrocks can be
     -- used as a standalone method in the package.
     
     -- If deg(f1,currVar) == 0, then f1 = 1.
     
     if degVar(f_(0,0),currVar) == 0 then (
	  print("Using deg(f1)=0 shortcut."); -- Debugging.
	  M = mutableIdentity(R, nCol);
	  apply(1..(nCol-1), i -> (M_(0,i) = -f_(0,i)));
	  return(matrix(M),1_R);
     );
     
     -- If nCol == 2, then (f1,f2) == R.
     
     if nCol == 2 then (
	  print("Using nCol=2 shortcut."); -- Debugging.
	  M = map(R^1) // f;
	  return(inverse(f || matrix{{-M_(1,0),M_(0,0)}}),1);
     );

     -- Use the general procedure if nCol > 2 and deg(f1,currVar) > 0.

     while degVar(f_(0,0),currVar) > 0 do (
     	  
	  -- Use f1 to reduce the degrees of each fi.
	  
          print("Entering while loop.  Deg(f1) = "|degVar(f_(0,0),currVar)); -- Debugging.
     	  for i from 1 to (nCol - 1) do (
	       r = degVar(f_(0,i),currVar) - degVar(f_(0,0),currVar);
	       print("Reducing the degree of f"|i+1); -- Debugging.
	       while r >= 0 do (
	       	    M = mutableIdentity(R,nCol);
	       	    M_(0,i) = -leadCoeffVar(f_(0,i),currVar)*currVar^r;
	       	    M_(i,i) = leadCoeffVar(f_(0,0),currVar);
	       	    f = f*matrix(M);
	       	    U = U*matrix(M);
	       	    r = r-1;
		    print(matrix(M));
	       );
	       print(U,f);
	       
	       -- Is fi a unit?  If so, swap it with f1 and finish.
	       
	       s = degVar(f_(0,i),currVar);
	       if (s == 0 and leadCoeffVar(f_(0,i),currVar) % I != 0) then (
		    print("f"|i+1|" has degree zero and is a unit."); -- Debugging.
		    M = mutableIdentity(R,nCol);
		    M_(0,0) = 0;
		    M_(i,i) = 0;
		    M_(i,0) = 1;
		    M_(0,i) = 1;
		    f = f*matrix(M);
		    U = U*matrix(M);
		    break;
	       );
	       
	       -- Check if any of the coefficients of fi
	       -- are units in the localization.
	       
     	       j = 0;
	       while (j <= s-1 and (flatten coefficients(f_(0,i),Variables=>{currVar}))#1_(j,0) % I == 0) do (
	     	    j = j+1;
	       );
	  
    	  -- If this terminates before j = s then the jth
    	  -- coefficient of fi is a unit in the localization.
    	  -- Use an elementary column operation to move fi
    	  -- to the f2 spot.
    
               if j < s then (
		    print("Found a unit coefficient in f"|i+1); -- Debugging.
	       	    M = mutableIdentity(R,nCol);
	       	    M_(1,1) = 0;
	       	    M_(i,i) = 0;
	       	    M_(i,1) = 1;
	       	    M_(1,i) = 1;
	       	    f = f*matrix(M);
	       	    U = U*matrix(M);
		    
	       -- Use suslinLemma to find g in (f1,f2)
	       -- whose leading coefficient with
	       -- respect to currVar is a unit
	       -- in the localization.
		    
		    print("Computing g."); -- Debugging.
		    g = suslinLemma(f_(0,0),f_(0,1),currVar,I);
		    N = matrix{{g}} // matrix{{f_(0,0),f_(0,1)}};
		    
	       -- Use g and N to make f3 have degree < f1
	       -- and have its leading coefficient be a
	       -- unit in the localization.    
		       
	       -- If the degree of f3 is greater than or
	       -- equal to the degree of g, then use g and
	       -- N to make f3 monic and make
	       -- deg(f3,currVar) < deg(f1,currVar).
		
		    if degVar(f_(0,2),currVar) >= degVar(g,currVar) then (
		    	 print("deg(f3) >= deg(g) case."); -- Debugging.
			 while degVar(f_(0,2),currVar) > degVar(g,currVar) do (
			      M = mutableIdentity(R,nCol);     
			      M_(0,2) = -leadCoeffVar(f_(0,2),currVar)*currVar^(degVar(f_(0,2),currVar)-degVar(g,currVar))*N_(0,0);
			      M_(1,2) = -leadCoeffVar(f_(0,2),currVar)*currVar^(degVar(f_(0,2),currVar)-degVar(g,currVar))*N_(1,0);
			      M_(2,2) = leadCoeff(g,currVar);
			      f = f*matrix(M);
			      U = U*matrix(M);
			 );		    
		    	 
	       -- Now that deg(f3,currVar) = deg(g,currVar),
	       -- make LC(f3) = LC(g).
			 
			 M = mutableIdentity(R,nCol);
			 M_(0,2) = (1_R-leadCoeffVar(f_(0,2),currVar))*N_(0,0);
			 M_(1,2) = (1_R-leadCoeffVar(f_(0,2),currVar))*N_(1,0);
			 M_(2,2) = leadCoeffVar(g,currVar);
			 f = f*matrix(M);
			 U = U*matrix(M);
		    );
	       
	       -- If the degree of f3 is smaller than the
	       -- degree of g, then just add g to f3 so
	       -- that the leading coefficient of f3 is
	       -- a unit and deg(f3,currVar) < deg(f1,currVar).
		    
		    if degVar(f_(0,2),currVar) < degVar(g,currVar) and leadCoeffVar(f_(0,2),currVar) % I == 0 then (
			 print("deg(f3) < deg(g) case."); -- Debugging.
			 M = mutableIdentity(R,nCol);
			 M_(0,2) = N_(0,0);
			 M_(1,2) = N_(1,0);
			 f = f*matrix(M);
			 U = U*matrix(M);
		    );	 
	       
	       -- Now swap f1 and f3.
	            
		    print("Swapping f1 and f3."); -- Debugging.
	       	    M = mutableIdentity(R,nCol);
		    M_(0,0) = 0;
		    M_(2,0) = 1;
		    M_(0,2) = 1;
		    M_(2,2) = 0;
		    f = f*matrix(M);
		    U = U*matrix(M);
		    break; -- Repeat the main while loop.
	       );
     	  );
     );
     
     -- When the main while loop terminates, f1 will be
     -- a unit in the localization.
     -- Use f1 to clear out the rest of the row.
     -- f1 will be a common denominator in the localization.

     M1 = (matrix{{1/f_(0,0)}}++map((frac(R))^(nCol-1)));
     M2 = mutableIdentity(R,nCol);
     apply(1..(nCol-1), i -> (M2_(0,i) = -f_(0,i)));
     U = U*M1*matrix(M2);
     return U;       
)


-- This computes a set of local solutions for a given unimodular row f.

getLocalSolutions = method()
getLocalSolutions(Matrix,List,RingElement) := (f,ringVars,currVar) -> (
     local I; local matrixList; local denomList; local R;
     R = coefficientRing(ring f)[ringVars];
     S = ring currVar;
     I = sub(ideal(0),R);
     maxIdeal = sub(findMaxIdeal(I),S);
     matrixList = new List from {};
     denomList = new List from {};
     (U,r) = horrocks(f,currVar,maxIdeal);
     I = ideal(sub(r,R));
     matrixList#0 = sub(U,frac(S));
     denomList#0 = sub(r,R);
     while I =!= R do (
	  maxIdeal = sub(findMaxIdeal(I),S);
	  (U,r) = horrocks(f,maxIdeal,currVar);
	  I = I+ideal(sub(r,R));
	  matrixList = append(matrixList,sub(U,frac(S)));
	  denomList = append(denomList,sub(r,R));
     );
     return(matrixList,denomList);
)


-- Method to patch together the local solutions obtained
-- by getLocalSolutions as in Logar-Sturmfels.
-- Do we really need denom#i^m as a common denominator?
-- It seems that Fabianska doesn't use this, at least
-- sometimes, and it makes the output simpler.
-- Patching code can definitely be improved.

patch = method();
patch(List,List,RingElement) := (matrixList,denomList,currVar) -> (
     local R; local m; local k; local g; local U;
     R = ring currVar;
     m = rank source matrixList#0; -- m = length of unimodular row.
     k = #matrixList; -- k = number of local solutions.
     denomList2 = new List from {};
     apply(0..(k-1), i -> (denomList2 = append(denomList2,(denomList#i)^m))); -- We can do better than ^m here.
     g = map(R^1) // matrix{denomList2};
     print(g);
     inverseList = new List from {};
     apply(0..(k-1), i -> (inverseList = append(inverseList,inverse(matrixList#i)))); -- Compute inverse for each local solution in frac(R).
     inverseDenom = new List from {};
     apply(0..(k-1), i -> (inverseDenom = append(inverseDenom,commonDenom(inverseList#i)))); -- Compute common denominators for inverse matrices.
     U = matrixList#0 * sub(sub(sub(inverseDenom#0*inverseList#0,R),{currVar => (currVar - currVar*(g_(0,0))*(denomList2#0))}),frac(R)) * (1/inverseDenom#0);
     apply(1..(k-1), i -> (U = U*(1/denomList#i)*sub(sub(sub((denomList#i)*(matrixList#i),R),{currVar => (currVar - (sum(0..(i-1), j -> currVar*g_(j,0)*denomList2#j)))}),frac(R))*(1/(inverseDenom#i))*sub(sub(sub((inverseDenom#i)*(inverseList#i),R),{currVar => (currVar - (sum(0..i, j -> currVar*g_(j,0)*denomList2#j)))}),frac(R))));
     return sub(U,R);  -- U is a unimodular matrix over R such that f*U does not involve currVar.
)

--------------------------------------------------
-- Input Functions
--------------------------------------------------

-- i.e.
-- computeFreeBasis( Module ) := M -> ( M := gens M; computeFreeBasis M );


beginDocumentation()

document {
     Key => computeFreeBasis, 
     Headline => ""
     } 

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///
end

uninstallPackage "QuillenSuslin"
restart
path = append(path, homeDirectory | "M2/Colorado-2010/")
installPackage("QuillenSuslin", UserMode => true) 