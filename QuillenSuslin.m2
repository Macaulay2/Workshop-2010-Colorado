newPackage(
	"QuillenSuslin",
    	Version => "0.1", 
    	Date => "August 08, 2010",
    	Authors => {
	     {Name => "Hirotachi Abo", Email => "abo@uidaho.edu", HomePage => "http://www.webpages.uidaho.edu/~abo/"},
	     {Name => "Brett Barwick", Email => "barwicjb@mailbox.sc.edu", HomePage => "http://www.math.sc.edu/~barwicjb/"},
	     {Name => "Branden Stone", Email => "bstone@math.ku.edu", HomePage => "http://www.math.ku.edu/~bstone"}	     
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
     return (coefficients(f,Variables =>{var}))#1_(0,0); 
)     
     

-- Returns the degree of a multivariate polynomial
-- with respect to a particular variable.

degVar = method()
degVar(RingElement,RingElement) := (f,var) -> (
     return (((degrees((coefficients(f,Variables=>{var}))#0))#1)#0)#0;
)


-- Finds the least common denominator of all entries of a matrix
-- over a fraction field by finding the LCM of all denominators.

commonDenom = method()
commonDenom(Matrix) := M -> (
     local nCol; local nRow; local denomList;
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
-- 9/7/2010: Fixed shortcut 2.2.1(2).

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
	  M1 = columnSwap(M1,0,s);
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
     s = scan ( #S, i -> ( 
	       if ideal S_i == R 
	       then break S_i;
	       )
	  );
     if s =!= null
     then (
	  print("Using shortcut 2.2.1(2).");
	  p1 = position(f, i -> (i == s_0));
	  p2 = position(f, i -> (i == s_1));
	  M1 = map(R^1) // matrix{s};
	  M2 = mutableIdentity(R,n);
     -- Swap so that the first two elements of g generate R.
	  M2 = columnSwap(M2,0,p1);
	  M2 = columnSwap(M2,1,p2);
	  M3 = mutableIdentity(R,n);
	  gSwap = g*matrix(M2);
	  M3_(0,0) = M1_(0,0);
	  M3_(1,0) = M1_(1,0);
	  M3_(0,1) = -gSwap_(0,1);
	  M3_(1,1) = gSwap_(0,0);
	  M4 = mutableIdentity(R,n);
	  apply(2..(n-1), i -> (M4_(0,i) = -(gSwap)_(0,i)));
	  U5 = matrix(M2)*matrix(M3)*matrix(M4);
	  return U5;
     );
    
     -- Fabianska shortcut 2.2.1(3).
     s = scan(n, i -> (if ideal submatrix'(g,,{i}) == R then break i));
     if s =!= null then (
	  print("Using shortcut 2.2.1(3).");
	  M1 = mutableIdentity(R,n);
	  M1 = columnSwap(M1,0,s);
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
     l = flatten entries (map(R^1) // g);
     w = scan( n, i -> ( if ideal l_i == R then break i ) );
     if w =!= null
     then (
	  print("Using shortcut 2.2.2(1).");
	  M1 = mutableIdentity(R,n);
	  M1 = columnSwap(M1,0,w);
	  M2 = mutableIdentity(R,n);
	  apply(0..(n-1), i -> (M2_(i,0) = (matrix{l}*matrix(M1))_(0,i)));
	  M3 = mutableIdentity(R,n);
	  apply(1..(n-1), i -> (M3_(0,i) = -(g*matrix(M1))_(0,i)));
	  U4 = matrix(M1)*matrix(M2)*matrix(M3);
	  return matrix U4;
	  );
     
     -- Fabianska shortcut 2.2.2(2).
     S = subsets(l,2);
     s = scan(n, i -> (if ideal S_i == R then break S_i;));
     if s =!= null then (
	  print("Using shortcut 2.2.2(2).");
	  p1 = position(l, i -> (i == s_0));
	  p2 = position(l, i -> (i == s_1));
	  M1 = map(R^1) // matrix{s};
	  M2 = mutableIdentity(R,n);
     -- Swap so that the first two elements of l generate R.
          M2 = columnSwap(M2,0,p1);
	  M2 = columnSwap(M2,1,p2);
	  M3 = mutableIdentity(R,n);
	  lSwap = matrix{l}*matrix(M2);
	  gSwap = g*matrix(M2);
	  apply(0..(n-1), i -> (M3_(i,0) = lSwap_(0,i)));
	  M3_(0,1) = -M1_(1,0);
	  M3_(1,1) = M1_(0,0);
	  M4 = mutableIdentity(R,n);
	  M4_(0,1) = -(-M1_(1,0)*gSwap_(0,0)+M1_(0,0)*gSwap_(0,1));
	  apply(2..(n-1), i -> (M4_(0,i) = -(gSwap)_(0,i)));
	  U5 = matrix(M2)*matrix(M3)*matrix(M4);
	  return U5;  	  
     );
)


-- This method takes a unimodular matrix phi over a PID and returns a unimodular matrix U such that phi*U = (I | 0).
-- This works as long as Macaulay2 computes the Smith normal form like I think it does.
-- Warning: May return unexpected results if R is not actually a PID.

qsAlgorithmPID = method()
qsAlgorithmPID(Matrix) := Matrix => phi -> (
     local B; local C; local D; local F; local G; local H1; local H2; local U'; local U; local V;
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
     local nrow; local ncol; local r; local ai; local Ai; local Ui;
     R = ring phi;
     nrow = rank target phi;
     ncol = rank source phi;
     r = ncol - nrow;
     
     -- If there is only one row, then just return the
     -- output of qsAlgorithmRow.
     
     if nrow == 1 then (
	  return qsAlgorithmRow(phi);
     );  
     
     -- Implements the shortcut for (p-1) x p unimodular
     -- matrices from Fabianska section 2.2.1.
     
     -- Invert and calculate row minors. (Use Cauchy-Binet formula.)
     if r == 1 then (
	  M = inverse(phi);
	  bottomRow = mutableMatrix(R,1,ncol);
	  for i from 0 to ncol-1 do bottomRow_(0,i) = (-1)^(ncol+1+i)*rowMinor(M,i);
	  bottomRow = matrix bottomRow;
	  print("Used shortcut 2.2.1 2");
	  return inverse(phi || bottomRow);
     );    
      
     Ai = phi;
     ai = Ai^{0};
     Ui = qsAlgorithmRow(ai);
     Ai = Ai*Ui;
     for i from 1 to nrow-1 do (
	  Bi = submatrix(Ai,{i..nrow-1},{i..ncol-1});
	  bi = Bi^{0};
	  Ui' = qsAlgorithmRow(bi);
	  idi = map(R^i);
	  Ui'' = idi++Ui';
	  Ui = Ui*Ui'';
	  Ai = Ai*Ui'';
     );
     Vi = prune image Ai;
     V = (gens Vi // map(R^nrow,R^ncol,Ai))|(map(R^(nrow-r),R^r,0_R)||map(R^r));
     Ui*V
)


-- General algorithm to compute solution to the unimodular
-- row problem using the procedure from Logar-Sturmfels.

qsAlgorithmRow = method()
qsAlgorithmRow(Matrix) := f -> (
     local R; local n; local varList; local U; local f; local currVar;
     
     -- If a shortcut applies, return it.
     
     if applyRowShortcut(f) =!= null then (
	  print("A shortcut method applies.");
	  return applyRowShortcut(f);
     );

     -- If not, enter the general algorithm.
     
     R = ring f;
     n = rank source vars R; -- n = number of variables.
     m = rank source f; -- m = length of the row.
     U = map(R^m);
     varList = flatten entries vars R;
     currVar = last varList; -- Set the last variable to be the current variable to eliminate.
     varList = take(varList,#varList - 1);
     
     print(varList,currVar);
     
     -- Determine if the coefficient ring is a field or not.
     
     
     if isField(coefficientRing(R)) == true then (
	  
	  -- Iteratively reduce the number of variables in f.
	  
	  while #varList >= 1 do (
	       
	       print("Entering the local loop. currVar = "|toString(currVar));
	       
	       s = scan(m, i -> (if degVar(f_(0,i),currVar) > 0 then break i;));
	       
	       -- If f doesn't involve currVar, then move to the next variable.
	       	  
	       if s =!= null then (
		    t = scan(m, i -> (if leadCoeffVar(f_(0,i),currVar) == 1 then break i;)); -- Does f have a component which is monic in currVar?
	       	    if t =!= null then (
	       	    	 print("f has a component which is monic with respect to "|currVar);
			 M1 = mutableIdentity(R,m);
			 M1 = columnSwap(M1,0,t);  -- Swap f1 and ft.
			 f = f*matrix(M1); -- Now f1 is monic in currVar.
			 U = U*matrix(M1); -- Record this transformation in U.
		    )
	       
	       	    else ( -- If f does not contain a component which is monic in currVar.
			 print("Does not contain monic component.  Performing normalization step.");
			 (f,subs,invSubs) = changeVar(f,varList,currVar); -- Normalize the row so that the first component is monic with respect to currVar.
		    	 print("The first element of the row is now monic in "|toString(currVar)|": "|toString(f));
		    );
	            print("Computing local solutions.");
		    localSolutions = getLocalSolutions(f,varList,currVar); -- Collect a list of unimodular matrices over frac(R) which solve the unimodular row problem for g.
		    print("Patching local solutions.");
		    U1 = patch(localSolutions,currVar); -- U1 is a unimodular matrix such that g*U does not involve currVar.
		    f = f*U1;
		    f = phi(f); -- Now f does not involve currVar.
		    print("Row now has one less variable: "|toString(f));
		    U = U*phi(U1); -- Update U.
	       );
	       
	       if applyRowShortcut(f) =!= null then(
		    print("A shortcut method applied.");
		    U2 = applyRowShortcut(f);
		    return U*U2;
	       );
	       
	       currVar = last varList; -- Set currVar to the next variable.
	       varList = take(varList,#varList - 1); -- Shorten the list of variables by one.
	  
	       -- Now repeat the loop until only one variable is left.
	  
	  );
     	  
	  -- The while loop will terminate when varList is empty, ie. the row only involves one variable.
     	  -- Then R = k[x1] is a PID, so we can use qsAlgorithmPID.
	  
	  return U*qsAlgorithmPID(f);
     );

     if coefficientRing(R) == ZZ then (
	  print("Doesn't work over ZZ yet.");  
     	  return null;
     );
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

-- 9/20/2010: Implemented normalization steps for various
-- situations where shortcuts are available.

changeVar = method()
changeVar( Matrix, RingElement ) := (f,currVar) -> (
     local R; local n; local m; local g; local M; local subs; local invSubs;
     local varList;
     R = ring f;
     varList = take(flatten entries vars R,position(flatten entries vars R, i -> (i == currVar))); -- Make a list of the variables in R 'before' currVar.
     n = rank source f; -- n = number of columns in f.
     m = #varList + 1; -- m = number of variables currently being considered.
     
     -- If n = 2, then we can easily transform f to (1,0).
     
     if n == 2 then (
	  print("Used n = 2 shortcut for normalization.");
	  g = map(R^1) // f;
	  M = mutableIdentity(R,2);
	  M_(0,0) = g_(0,0);
	  M_(1,0) = g_(1,0);
	  M_(0,1) = -f_(0,1);
	  M_(1,1) = f_(0,0);
	  return(matrix M,vars R,vars R);
     );

     -- If a component already equals 1, then move it to the front.
     -- This is just to make the degMatrix in the next step
     -- work out nicely.  ie.  This removes the possibility that
     -- a component of f is monic of degree zero.
     
     s = scan(n, i -> (if f_(0,i) == 1_R then break i;));
     
     if s =!= null then (
	  M = mutableIdentity(R,n);
	  M = columnSwap(M,0,s);
	  return(matrix M,vars R,vars R);
     );
     
     -- If none of the components are the constant 1, we create
     -- a matrix (degMatrix) whose (i,j)th entry is zero if
     -- f_(0,j) is not monic in varList#i (currVar counts as i = m-1)
     -- and if degMatrix_(i,j) != 0, then degMatrix_(i,j) is the
     -- degree of f_(0,j) viewed as a polynomial in varList#i.
     -- The goal is to move the smallest degree monic component
     -- to the front of f.
     
     degMatrix = mutableMatrix(R,m,n);
     
     for i from 0 to m-2 do (
	  for j from 0 to n-1 do (
	       if leadCoeffVar(f_(0,j),varList#i) == 1 then (
		    degMatrix_(i,j) = degVar(f_(0,j),varList#i);
	       );
	  );
     );
     apply(0..n-1, i -> (if leadCoeffVar(f_(0,i),currVar) == 1 then (degMatrix_(m-1,i) = degVar(f_(0,i),currVar););));
     
     -- Now that degMatrix has been constructed, go through
     -- and check if any nonzero entries exist (a nonzero
     -- entry represents a row element which is monic in
     -- one of the variables.)
     
     minEntry = (null,null,null);
     apply(0..(m-1), i -> (apply(0..(n-1), j -> (if degMatrix_(i,j) > 0 then ( minEntry = (i,j,degMatrix_(i,j)); break;);))));
     
     if minEntry =!= (null,null,null) then (
     	  apply(minEntry#0..(m-1), i -> (apply(0..(n-1), j -> (if degMatrix_(i,j) > 0 and degMatrix_(i,j) < minEntry#2 then minEntry = (i,j,degMatrix_(i,j))))));  
     	  M = mutableIdentity(R,n);
	  M = columnSwap(M,0,minEntry#1);
	  subs = new MutableMatrix from vars R;
	  subs = columnSwap(subs,minEntry#0,m-1); -- This map just transposes the two variables.  It is its own inverse.
	  return(matrix M,matrix subs,matrix subs);
     );

     -- If minEntry == (null,null,null), this means that
     -- there were not any components of f that were already
     -- monic in one of the variables.
     
     print("No component of the row was monic in any of the variables.");
     
     -- The last normalization shortcut is to check whether
     -- a smaller subset of the row elements generate the
     -- entire ring.  If so, then we can use a unimodular
     -- transformation to get 1 in the first position of f.
     -- This is the same as shortcut 2.2.1(3) in applyRowShortcut.
     
     s = scan(n, i -> (if ideal submatrix'(f,,{i}) == R then break i));
     if s =!= null then (
	  M1 = mutableIdentity(R,n);
	  M1 = columnSwap(M1,0,s);
          fSwap = f*matrix(M1);
	  -- Now fSwap_(0,1) = 0.
	  h = map(R^1) // submatrix'(fSwap,,{0});
	  M2 = mutableIdentity(R,n);
	  apply(1..(n-1), i -> (M2_(i,0) = (1-fSwap_(0,0))*h_(i-1,0)));
	  M3 = mutableIdentity(R,n);
	  apply(1..(n-1), i -> (M3_(0,i) = -fSwap_(0,i)));
	  M = matrix(M1)*matrix(M2)*matrix(M3);
	  return (M,vars R,vars R);
     );
     
     -- We will split into two cases, based on whether the
     -- coefficient ring is a field or ZZ.
     
     if isField(coefficientRing(R)) == true then (
	  print("Normalizing over QQ.");
	  
	  -- Method 1: Move the smallest total degree element
	  -- to the front, multiply by the inverse of the
	  -- leading coefficient, then make the change of
	  -- variables.
	  print("Using method 1.");
	  
	  
	  
	  
	  -- Method 2: Check if the row has 2 integer leading
	  -- coefficients (when considered in terms of total
	  -- degrees) which are relatively prime.  If so,
	  -- find a relation which converts the first entry
	  -- to a monic polynomial when considering total degrees.
	  print("Using method 2.");
	  
	  
	  
     );

     if coefficientRing(R) === ZZ then (
	  print("Normalizing over ZZ.");
	  
	  
	  
	  
	  
	  
	  
	  
     );

     print("Unsupported coefficient ring.  Try QQ or ZZ.");
     
)


-- Effective version of Suslin's Lemma which takes two
-- polynomials with deg(f) = s and deg(g) <= s-1, f monic,
-- and one of the coefficients of g a unit, and produces
-- a polynomial h in (f,g) with deg(h) = deg(g) and the
-- leading coefficient of h is a unit in R_I. 

suslinLemma = method()
suslinLemma(RingElement,RingElement,RingElement,Ideal) := (f,g,var,I) -> (
     local lcf; local lcg;
     lcf = leadCoeffVar(f,var);
     lcg = leadCoeffVar(g,var);
     while lcg % I == 0 do (
	  g = lcf*var^(degVar(f,var)-degVar(g,var))*g - lcg*f;
	  print(g);
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
     local R; local g; local nCol; local U;
     R = ring f;
     
     -- Throw errors if f does not meet requirements.
     
     if leadCoeffVar(f_(0,0),currVar) != 1_R then (
	  print("Error: The first element of the row is not monic in the given variable.");
	  return null;
     );

     if isUnimodular(f) == false then (
	  print("Error: The given row is not unimodular.");
	  return null;
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
	  return(matrix(M));
     );
     
     -- If nCol == 2, then (f1,f2) == R.
     
     if nCol == 2 then (
	  print("Using nCol=2 shortcut."); -- Debugging.
	  M = map(R^1) // f;
	  return(inverse(f || matrix{{-M_(1,0),M_(0,0)}}));
     );

     -- Use the general procedure if nCol > 2 and deg(f1,currVar) > 0.

     while degVar(f_(0,0),currVar) > 0 do (
     	  
	  -- Use f1 to reduce the degrees of each fi.
	  
          print("Entering while loop.  Deg(f1) = "|degVar(f_(0,0),currVar)); -- Debugging.
     	  for i from 1 to (nCol - 1) do (
	       r = degVar(f_(0,i),currVar) - degVar(f_(0,0),currVar);
	       print r;
	       print("Reducing the degree of f"|i+1); -- Debugging.
	       while r >= 0 do (
	       	    M = mutableIdentity(R,nCol);
	       	    M_(0,i) = -leadCoeffVar(f_(0,i),currVar)*currVar^r;
	       	    M_(i,i) = leadCoeffVar(f_(0,0),currVar);
	       	    f = f*matrix(M);
	       	    U = U*matrix(M);
	       	    r = r-1;
	       );
	       
	       -- Is fi a unit in the smaller polynomial ring?  If so, swap it with f1 and finish.
	       
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
	       while (j <= s and (flatten coefficients(f_(0,i),Variables=>{currVar}))#1_(j,0) % I == 0) do (
	     	    j = j+1;
	       );
	  
    	  -- If this terminates before j = s+1 then the jth
    	  -- coefficient of fi is a unit in the localization.
    	  -- Use an elementary column operation to move fi
    	  -- to the f2 spot.
 
	       if j < s+1 then (
		    print("Found a unit coefficient in f"|i+1); -- Debugging.
	       	    M = mutableIdentity(R,nCol);
	       	    M = columnSwap(M,1,i);
	       	    f = f*matrix(M);
	       	    U = U*matrix(M);
		
	       -- If the leading coefficient of f2 is already
	       -- a unit, use it to reduce the degree of f1.
	       
	            if leadCoeffVar(f_(0,1),currVar) % I != 0 then (
		    	 print leadCoeffVar(f_(0,1),currVar);
			 print("Leading coefficient of f2 already a unit.  Using f2 to reduce degree of f1."); -- Debugging.
			 while degVar(f_(0,0),currVar) >= degVar(f_(0,1),currVar) do (
			      M = mutableIdentity(R,nCol);     
			      M_(0,0) = leadCoeffVar(f_(0,1),currVar);
			      M_(1,0) = -leadCoeffVar(f_(0,0),currVar)*currVar^(degVar(f_(0,0),currVar)-degVar(f_(0,1),currVar));
			      f = f*matrix(M);
			      U = U*matrix(M);
			 );
	            );    
	       
	       -- If the leading coefficient of f2 is not
	       -- a unit, then use suslinLemma to find g
	       -- in (f1,f2) whose leading coefficient with
	       -- respect to currVar is a unit in the
	       -- localization.
		    
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
			      M_(2,2) = leadCoeffVar(g,currVar);
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
		    M = columnSwap(M,0,2);
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
     print("Using horrocks with maximal ideal "|toString(maxIdeal)|" with respect to the variable "|toString(currVar));
     U = horrocks(f,currVar,maxIdeal);
     I = ideal(sub(commonDenom(U),R));
     matrixList = append(matrixList,sub(U,frac(S)));
     while I =!= R do (
	  maxIdeal = sub(findMaxIdeal(I),S);
	  print("Denominators did not generate the unit ideal.  Repeating horrocks with ideal "|toString(maxIdeal));
	  U = horrocks(f,currVar,maxIdeal);
	  I = I+ideal(sub(commonDenom(U),R));
	  matrixList = append(matrixList,sub(U,frac(S)));
     );
     return matrixList;
)


-- Method to patch together the local solutions obtained
-- by getLocalSolutions as in Logar-Sturmfels.

-- Do we really need denom#i^m as a common denominator?
-- It seems that Fabianska doesn't use this, at least
-- sometimes, and it makes the output simpler.
-- Patching code can definitely be improved.

-- 9/6/2010: The matrix n is added to improve this issue.
-- Still need to write down a proof that this always works.

patch = method();
patch(List,RingElement) := (matrixList,currVar) -> (
     local R; local m; local k; local g; local U; local n; local j;
     local inverseList; local denomList; local inverseDenom; local deltaDenom;
     R = ring currVar;
     m = rank source matrixList#0; -- m = length of unimodular row.
     k = #matrixList; -- k = number of local solutions.
     inverseList = new List from {};
     apply(0..(k-1), i -> (inverseList = append(inverseList,inverse(matrixList#i)))); -- Compute inverse for each local solution in frac(R).
     denomList = new List from {};
     apply(0..(k-1), i -> (denomList = append(denomList,commonDenom(matrixList#i))));
     inverseDenom = new List from {};
     apply(0..(k-1), i -> (inverseDenom = append(inverseDenom,commonDenom(inverseList#i)))); -- Compute common denominators for inverse matrices.
     n = mutableMatrix(ZZ,1,k);
     apply(0..(k-1), i -> (while inverseDenom#i % ((denomList#i)^(n_(0,i)+1)) == 0 do (n_(0,i) = n_(0,i) + 1;);)); -- Set n_(0,i) to be the number of times that denomList#i occurs as a factor of inverseDenom#i.
     deltaDenom = new List from {};
     apply(0..(k-1), i -> (deltaDenom  = append(deltaDenom,(denomList#i)^(n_(0,i)+1))));
     g = map(R^1) // matrix{deltaDenom};
     U = matrixList#0 * sub(sub(sub(inverseDenom#0*inverseList#0,R),{currVar => (currVar - currVar*(g_(0,0))*(deltaDenom#0))}),frac(R)) * (1/inverseDenom#0);
     apply(1..(k-1), i -> (U = U*(1/denomList#i)*sub(sub(sub((denomList#i)*(matrixList#i),R),{currVar => (currVar - (sum(0..(i-1), j -> currVar*g_(j,0)*deltaDenom#j)))}),frac(R))*(1/(inverseDenom#i))*sub(sub(sub((inverseDenom#i)*(inverseList#i),R),{currVar => (currVar - (sum(0..i, j -> currVar*g_(j,0)*deltaDenom#j)))}),frac(R))));
     return sub(U,R);  -- U is a unimodular matrix over R such that f*U does not involve currVar (it is the same as f evaluated when currVar = 0).
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