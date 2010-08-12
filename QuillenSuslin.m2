newPackage(
	"QuillenSuslin",
    	Version => "0.1", 
    	Date => "August 08, 2010",
    	Authors => {
	     {Name => "Hirotachi Abo", Email => "abo@uidaho.edu", HomePage => "http://www.webpages.uidaho.edu/~abo/"},
	     {Name => "Brett Barwick", Email => "barwicjb@mailbox.sc.edu", HomePage => "http://www.math.sc.edu/~barwicjb/"},
	     {Name => "Branden Stone", Email => "", HomePage => ""}	     
	     },
    	Headline => "QuillenSusulin",
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
     "changeVar"     
}

-- Core prgram to compute the free basis
-- Needs QSAlgorithm
--
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
     Ai)


-- Shortcuts from fabianska's PhD thesis
-- 
-- I hope this works.

applyRowShortcut = method()
applyRowShortcut(Matrix) := g -> (
     R := ring g;
     f := flatten entries g;
     n := #f;
          
     -- fabianska shortcut 2.2.1(1)
     s := scan( n, i -> ( if ideal f_i == R then break i ) );
     
     if s =!= null
     then (
	  F := (matrix {{f_s*1_R}})^-1;
	  U1 := mutableIdentity(R,n);
	  scan( n, i -> ( U1_(s,i) = -F_(0,0)*f_i ) );
	  U1_(s,s) = F_(0,0);
	  return matrix U1;
	  );
     
     -- fabianska shortcut 2.2.1(2)
     S := subsets(f,2);
     h := scan ( #S, i -> ( 
	       if ideal S_i == R 
	       then break S_i;
	       )
	  );
     if h =!= null
     then (
	  ss := position( f, i -> ( i == h_0 ) );
	  t := position( f, i -> ( i == h_1 ) );
	  	  
	  H := 1_R//gens ideal h;
	  W := mutableIdentity(R,n);
	  W_(ss,0) = H_(0,0);
	  W_(t,0) = H_(1,0);
	  W_(ss,1) = -h_1;
	  W_(t,1) = h_0;
	  if ( ss>1 or t>1 )
	  then (
	       r := first rsort {ss,t};
	       W_(1,1) = 0;
	       W_(1,r) = 1;
	       W_(r,r) = 0;
	       );
	  G := delete( h_1, delete( h_0, f ) );
	  V := mutableIdentity(R,n);
	  scan(2..(n-1), i -> ( V_(0,i) = -G_(i-2) ) );
	  U2 := matrix W*matrix V;
	  return U2;
	  );
)

-- Compute the ideal of maximal minors of a matrix.

maxMinors = method()
maxMinors(Matrix) := M -> (
     local R; local i; 
     R = ring(M);
     i = min({rank target M, rank source M});
     while minors(i,M) == 0 and i > 0 do i=i-1;
     return minors(i,M);
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
-- U*N is the matrix of the form (I | 0).  This however needs qsAlgorithmRow.

qsAlgorithm = method() 
qsAlgorithm(Matrix) := Matrix => phi -> (
     R := ring phi;
     nrow := rank target phi;
     ncol := rank source phi;
     r := ncol - nrow;
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

-- Find's a maximal ideal containing a given ideal
-- Only works over QQ
-- Quick and dirty method thanks to Jason
findMaxIdeal = method()
findMaxIdeal( Ideal ) := I -> (
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

-- Changes variables according with Nagata's theorem (Lemma 2.3.1, Fabianska)
-- Outputs: (1) new unimodular row with leading term of first entry a pure power
-- of the "last" variable. (2) a function to reverse the change of variable.
--
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




-- This computes a set of local solutions for a given unimodular row f.
-- This still needs localSolution to be implemented.
{*
getLocalSolutions = method()
getLocalSolutions(Matrix) := f -> (
     local I; local matrixList; local rList;
     I = ideal(0);
     matrixList = new List from {};
     rList = new List from {};
     (U,r) = localSolution(f,I);
     I = ideal(r);
     matrixList#0 = U;
     rList#0 = r;
     while I =!= R do (
	  (U,r) = localSolution(f,I);
	  I = I+ideal(r);
	  matrixList = append(matrixList,U);
	  rList = append(rList,r);
     )
     return(matrixList,rList);
)
*}

--------------------------------------------------
--------------------------------------------------
-- Input Functions
--------------------------------------------------
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