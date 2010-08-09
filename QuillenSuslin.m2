newPackage(
	"QuillenSuslin",
    	Version => "0.1", 
    	Date => "August 08, 2010",
    	Authors => {
	     {Name => "Hirotachi Abo", Email => "abo@uidaho.edu", HomePage => "http://www.webpages.uidaho.edu/~abo/"},
	     {Name => "Brett Barwick", Email => "", HomePage => ""},
	     {Name => "Branden Stone", Email => "", HomePage => ""}	     
	     },
    	Headline => "QuillenSusulin",
    	DebuggingMode => true
    	)

export {}

-- Core prgram to compute the free basis
-- Needs QSAlgorithm
--
computeFreeBasis = method()
computeFreeBasis(Matrix) := Matrix => phi -> (
     R := ring phi;
     fphi := res coker phi;
     p := length fphi;
     Ai := fphi.dd_p
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