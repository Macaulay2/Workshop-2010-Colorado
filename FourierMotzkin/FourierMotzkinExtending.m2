loadPackage "FourierMotzkin"
getFilename = () -> (
     filename := temporaryFileName();
     while fileExists(filename) or fileExists(filename|".ine") or fileExists(filename|".out") do filename = temporaryFileName();
     filename)
	 
putMatrix = method()
putMatrix (File, Matrix) := (F,A) ->(
    
	F << "polytope" << endl;
	F << "H-representation" << endl;
	F << "begin" << endl;
	m := numColumns A;
	n := numRows A;
	A = matrix({toList(m:0)})||A;
	F << m << " " << n+1 << " rational" << endl;
	
	L := entries transpose A;
     for i from 0 to m-1 do (
	  for j from 0 to n do (
	       F << L#i#j << " ";
	       );
	  F << endl;
	  );
	
	F << "end" << endl;
)

putMatrix (File, Matrix, Matrix) := (F,C,B) -> (
     	F << "polytope" << endl;
	F << "H-representation" << endl;
	F << "linearity " << numColumns B << " ";
	apply(numColumns B, l-> F << l+1 << " ");
	F << endl;
	F << "begin" << endl;
	A := B|C;
	m := numColumns A;
	n := numRows A;
	A = matrix({toList(m:0)})||A;
	F << m << " " << n+1 << " rational" << endl;
	L := entries transpose A;
        for i from 0 to m-1 do (
	  for j from 0 to n do (
	       F << L#i#j << " ";
	       );
	  F << endl;
	  );
	
	F << "end" << endl;
	)


-- divides a list of integers by their gcd.
primitive = method();
primitive List := List => L -> (
     -- finding greatest common divisor
     n := #L-1;
     g := abs(L#n);
     while (n > 0) do (
	  n = n-1;
	  g = gcd(g, L#n);
	  if g === 1 then n = 0);
     if g === 1 then L 
     else apply(L, i -> i // g))

-- Converts a list of 'QQ' to 'ZZ' by multiplying by a common denominator
toZZ = method();
toZZ List := List => L -> (
     -- finding common denominator
     d := apply(L, e -> denominator e);
     l := lcm d;
     apply(L, e -> (numerator(l*e))))


compare = method()
compare String := filename ->(
     D := getMatrix(filename);
     A := cdd D;
     B := lrs D;
     << numRows A << "  "<< numColumns A << endl;
     A = matrix apply(select(transpose entries A, a->a#0==0),l-> l);
     << numRows A << "  "<< numColumns A << endl;
     << numRows B << "  "<< numColumns B << endl;
     B = matrix apply(select(transpose entries B, b->b#0==0),l-> l);
     << numRows B << "  " << numColumns B << endl;
     -- << class A << endl;
     -- << A << endl << B << endl;
     norm(promote(A-B,RR))
     )

getMatrixFromFile = method()
getMatrixFromFile String := (filename) -> (
     L := (separateRegexp("begin|end", get filename))#1;
     M := select(separateRegexp("[[:space:]]", L), m->m=!="");
     m := value( M#1);
     transpose matrix sort pack_m apply(drop(M,3), m-> lift(promote(value replace("E\\+?","e",m),RR),QQ))
)

getMatrix = method()
getMatrix String := (filename) -> (
     -- << get filename << endl;
     L := separateRegexp("linearity|begin|end", get filename);
     local m, M;
     if #L==3 then (
	  L = L#1;
     	  M = select(separateRegexp("[[:space:]]", L), m->m=!="");
     	  m = value( M#1);
     	  (sort transpose matrix apply(select(pack_m apply(drop(M,3), m-> lift(promote(value replace("E\\+?","e",m),RR),QQ)),i-> i#0==0),l->primitive drop(l,1)),matrix {{0}})
     ) else (
     	  lin := apply(drop(select(separateRegexp("[[:space:]]", L#1),m-> m=!=""),1), l-> (value l)-1);
	  M = select(separateRegexp("[[:space:]]", L#2), m->m=!="");
     	  m = value( M#1);
     	  mat :=  pack_m apply(drop(M,3), m-> lift(promote(value replace("E\\+?","e",m),RR),QQ));
	  linearity := sort transpose matrix apply(mat_lin, l-> primitive drop(l,1));
	  r := select(toList(0..#mat-1), n-> not member(n,lin));
	  rays := sort transpose matrix apply(select(mat_r, l-> l#0==0),l->primitive drop(l,1));
	  (rays, linearity)
	  )
)

	 
lrs = method()
lrs Matrix := Matrix => A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".ine");
     putMatrix(F,-A);
     close F;
     execstr = "lrs " |rootPath | filename | ".ine " | rootPath | filename | ".ext" ;
     run execstr;
     getMatrix (filename | ".ext")
     )
lrs (Matrix,Matrix) := Matrix => (A,B) ->(
     if B==0 then return cdd A else(
      filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".ine");
     putMatrix(F,-A,B);
     close F;
     execstr = "lrs " |rootPath | filename | ".ine " | rootPath | filename | ".ext" ;
     run execstr;
     getMatrix (filename | ".ext")
     ))

cdd = method()
cdd Matrix := Matrix => A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".ine");
     putMatrix(F,-A);
     close F;
     execstr = "lcdd " |rootPath | filename | ".ine " | rootPath | filename | ".ext" ;
     run execstr;
     getMatrix (filename | ".ext")
     )
cdd (Matrix, Matrix) := Matrix => (A,B) ->(
     if B==0 then return cdd A else(
       filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".ine");
     putMatrix(F,-A,B);
     close F;
     execstr = "lcdd " |rootPath | filename | ".ine " | rootPath | filename | ".ext" ;
     run execstr;
     getMatrix (filename | ".ext")
     ))
     

end

restart
load "FourierMotzkinExtending.m2"
loadPackage "FourierMotzkin"
f = fourierMotzkin B
sort f#0
lrs B
cdd B
viewHelp FourierMotzkin



-- Good examples
compare "in2.ine"
compare "in3.ine"
compare "cyc.ine"
compare "cube.ine"
compare "cube2.ine"
compare "cross4.ine"
compare "cubetop.ine"

-- Bad examples
compare "in4.ine"
compare "in5.ine"
compare "in6.ine"
compare "in7.ine"
compare "mit31_20.ine"

A=time sort (fourierMotzkin getMatrix "in5.ine")#0
lrs getMatrix "in5.ine"
C=time sort submatrix((cdd getMatrix "in5.ine"),{1..10},{0..91})
C = transpose matrix apply(transpose entries C,l->primitive toZZ l);
C
A-C
B=sort submatrix((cdd getMatrix "in4.ine"),{1..8},{0..53})
B = transpose matrix apply(transpose entries B,l->primitive toZZ l);
 B
A-B
cdd getMatrixFromFile "in5.ine"
fourierMotzkin getMatrixFromFile "cyc.ine"

restart
load "FourierMotzkinExtending.m2"
C = transpose matrix{{1,1,0}, {0,1,1}}
H = transpose matrix{{1,0,-1}}
C|H
fourierMotzkin (C,H)
cdd(C,H)

C = transpose matrix{{1,0,3,1},{1,1,0,7},{1,2,1,1}}
fourierMotzkin C
D = transpose matrix apply(entries transpose C, l-> reverse l)
G = cdd D
lrs lrs lrs lrs C
cdd cdd cdd cdd C

C = transpose random(ZZ^5, ZZ^8, Density=>.5)
fourierMotzkin C
cdd C
fourierMotzkin fourierMotzkin lrs C

cdd(C,H)
lrs(C,H)
P = fourierMotzkin fourierMotzkin (C,H)
assert(P#0 == transpose matrix{{0,1,1}})
assert(P#1 == H)
(matrix {{0}})==0
