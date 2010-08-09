newPackage(
    "BenchmarkGb",
    Version => "0.1",
    Date => "",
    Authors => {{Name => "Franziska Hinkelmann",
    Email => "",
    HomePage => ""}},
    Headline => "",
    DebuggingMode => true
    )

loadPackage "gbHelper"
export {runBenchmark, makeBooleanNetwork}

-- Code here

-- function generates random boolean networks
makeBooleanNetwork = method()
makeBooleanNetwork (QuotientRing, ZZ, ZZ) := Matrix => (R, valence, nterms) -> (
  -- R should be a boolean ring
  -- output: a random finite dynamical system
  -- where each function depends on up to 'valence' variables
  -- and 'nterms' terms
  choices := subsets(gens R, valence);
  ll := for x in gens R list (
    r := random (#choices);
    inputs := choices#r;
    allelems := subsets inputs;
    allelems = allelems/product;
    nt := 1 + random(nterms);
    -- random( allelems ) might pick the same monomial twice
    -- TODO fix that!
    sum for i from 1 to nt list allelems#(random (#allelems))
  );
  matrix(R, {ll})
)

runBenchmark = method()
runBenchmark Ideal := Ideal => I -> (
  runBenchmark(I, "stdout")
)

runBenchmark (Ideal,String) := Ideal => (I,ff) -> (
 R = ambient ring I;
 p := char R;
 assert( p == 2 );
 FP := ideal apply( gens R, x -> x^2 + x);

 Rlex = ZZ/(char R)[gens R, MonomialOrder=>Lex];
 T := timing gens gb( sub( I, Rlex) + sub( FP, Rlex) );
 tt := first T;
 G := last T;
 print ("Lex Order of (I+FP):\t\t\t\t" | toString tt | " seconds.");
 ff << "Lex Order of (I+FP):\t\t\t\t" << toString tt << " seconds." << endl;

 RgRevLex = ZZ/(char R)[gens R, MonomialOrder=>GRevLex];
 T = timing gens gb( sub( I, RgRevLex) + sub( FP, RgRevLex) );
 tt = first T;
 G = ideal last T;
 print ("GRevLex Order of (I+FP):\t\t\t" | toString tt | " seconds.");
 ff << "GRevLex Order of (I+FP):\t\t\t" << toString tt << " seconds." << endl;

 T = timing gens gb( sub( G, Rlex) + sub( FP, Rlex) );
 tt = first T;
 G = ideal last T;
 print ("Lex order from GRevLex basis of (I+FP):\t\t" | toString tt | " seconds.\n");
 ff << "Lex order from GRevLex basis of (I+FP):\t\t" << toString tt << " seconds.\n" << endl;

 QRlex = Rlex/ sub( FP, Rlex);
-- T = timing gens gb( sub( I, QRlex));
-- tt = first T;
-- G = last T;
-- print ("Quotient Ring Lex Order:\t\t\t" | toString tt | " seconds.");
--
 QRgRevLex = RgRevLex/ sub( FP, RgRevLex);
-- T = timing gens gb( sub( I, QRgRevLex));
-- tt = first T;
-- G = last T;
-- print ("Quotient Ring GRevLex Order:\t\t\t" | toString tt | " seconds.");
--
-- T = timing gens gb( sub( G, QRlex));
-- tt = first T;
-- G = last T;
-- print ("Quotient Ring Lex order from GRevLex basis:\t\t\t" | toString tt | " seconds.\n");
 
 T = timing gens gb( sub( I, QRlex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
 print ("Quotient Ring Lex Order, Sugarless:\t\t" | toString tt | " seconds.");
 ff << "Quotient Ring Lex Order, Sugarless:\t\t" << toString tt << " seconds." << endl;

 T = timing gens gb( sub( I, QRgRevLex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
 print ("Quotient Ring GRevLex Order, Sugarless:\t\t" | toString tt | " seconds.");
 ff << "Quotient Ring GRevLex Order, Sugarless:\t\t" << toString tt << " seconds." << endl;

 T = timing gens gb( sub( G, QRlex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
 print ("Quotient Ring Lex order from GRevLex basis, Sugarless:\t\t" | toString tt | " seconds.\n");
 ff << "Quotient Ring Lex order from GRevLex basis, Sugarless:\t\t" << toString tt << " seconds.\n" << endl;
 
 T = timing gbBoolean I;
 tt = first T;
 G = last T;
 print ("gbBoolean:\t\t\t\t\t" | toString tt | " seconds.\n\n");
 ff << "gbBoolean:\t\t\t\t\t" << toString tt << " seconds.\n\n" << endl;

 G
)


  
beginDocumentation()

doc ///
Key
  (BenchmarkGb)
  BenchmarkGb
Headline
  Run groebner basis computations in several monomial orders
Description
  Text
    Runs and times gb computations for an ideal in several monomials
    orders
  Example
Caveat
SeeAlso
///

doc ///
Key
  runBenchmark
  (runBenchmark,Ideal)
Headline
  run groebner basis computations in several monomial orders
Usage
  G = runBenchmark I
Inputs
  I:Ideal
    Ideal to compute the basis for
Outputs
  G:Ideal
    Basis in Lex order
Consequences
Description
  Text
    Run Groebner Basis computation in several rings and in several monomial orders. FP are the field polynomials, 
    i.e., $x + x^2$. The quotient ring is the ambient ring of the ideal mod the field polynomials. 
  Example
    R = ZZ/2[x,y,z];
    I = ideal(x+y,x);
    runBenchmark I
  Code
  Pre
Caveat
  The ring must have characteristic 2, because we mod out by the field polynomials.
SeeAlso
  (BenchmarkGb)
  "BooleanGB"
///

doc ///
Key
  makeBooleanNetwork 
  (makeBooleanNetwork, QuotientRing, ZZ, ZZ)
Headline
  generate a random ideal in a quotient ring 
Usage
  I = makeBooleanNetwork( QR, valence, nterms)
Inputs
  QR:QuotientRing
    a quotient ring with char 2
  valence:ZZ
    number of variables involved in each generator
  nterms:ZZ
    number of terms in each generator
Outputs
  G:Matrix
    a random ideal
Consequences
Description
  Text 
    Generate a random network
  Example
    R = ZZ/2[x,y,z]/(x^2+x, y^2+y, z^2+z)
    makeBooleanNetwork(R, 2, 2)
  Code
  Pre
Caveat
SeeAlso
  (BenchmarkGb)
  "BooleanGB"
///

TEST ///
  R = ZZ/2[x,y,z]
  I = ideal(x+y,x)
  runBenchmark I 
///

TEST ///
  R = ZZ/2[x,y,z]/(x^2+x, y^2+y, z^2+z)
  makeBooleanNetwork(R, 2, 2)
///

TEST ///
  S = ZZ/2[a1,a2,a3,a4,b1,b2,b3,b4,c1,c2,c3,c4,d1,d2,d3,d4,e1,e2,e3,e4,f1,f2,f3,f4,g1,g2,g3,g4,h1,h2,h3,h4,i1,i2,i3,i4,j1,j2,j3,j4,k1,k2,k3,k4,l1,l2,l3,l4,m1,m2,m3,m4,n1,n2,n3,n4,q1,q2,q3,q4,p1,p2,p3,p4, MonomialOrder=>Lex]
  II0 = ideal {a1+a2+a3+a4-1,a1*a2, a1*a3, a1*a4, a2*a3, a2*a4, a3*a4,  b1+b2+b3+b4-1,b1*b2, b1*b3, b1*b4, b2*b3, b2*b4, b3*b4, c1+c2+c3+c4-1,a1*a2, c1*c3, c1*c4, c2*c3, c2*c4, c3*c4, d1+d2+d3+d4-1,d1*d2, d1*d3, d1*d4, d2*d3, d2*d4, d3*d4, e1+e2+e3+e4-1,e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4, f1+f2+f3+f4-1,f1*f2, f1*f3, f1*f4, f2*f3, f2*f4, f3*f4, g1+g2+g3+g4-1,g1*g2, g1*g3, g1*g4, g2*g3, g2*g4, g3*g4, h1+h2+h3+h4-1,h1*h2, h1*h3, h1*h4, h2*h3, h2*h4, h3*h4, i1+i2+i3+i4-1,i1*i2, i1*i3, i1*i4, i2*i3, i2*i4, i3*i4, j1+j2+j3+j4-1,j1*j2, j1*j3, j1*j4, j2*j3, j2*j4, j3*j4, k1+k2+k3+k4-1,k1*k2, k1*k3, k1*k4, k2*k3, k2*k4, k3*k4, l1+l2+l3+l4-1,l1*l2, l1*l3, l1*l4, l2*l3, l2*l4, l3*l4, m1+m2+m3+m4-1,m1*m2, m1*m3, m1*m4, m2*m3, m2*m4, m3*m4, n1+n2+n3+n4-1,n1*n2, n1*n3, n1*n4, n2*n3, n2*n4, n3*n4, q1+q2+q3+q4-1, q1*q2, q1*q3, q1*q4, q2*q3, q2*q4, q3*q4, p1+p2+p3+p4-1,p1*p2, p1*p3, p1*p4, p2*p3, p2*p4, p3*p4, a1+b1+c1+d1-1,  a1*b1, a1*c1, a1*d1, b1*c1, c1*d1, a2+b2+c2+d2-1, a2*b2, a2*c2, a2*d2, b2*c2, c2*d2,a3+b3+c3+d3-1, a3*b3, a3*c3, a3*d3, b3*c3, c3*d3,a4+b4+c4+d4-1, a4*b4, a4*c4, a4*d4, b4*c4, c4*d4,e1+f1+g1+h1-1, e1*f1, e1*g1, e1*h1, f1*g1, g1*h1,e2+f2+g2+h2-1, e2*f2, e2*g2, e2*h2, f2*g2, g2*h2, e3+f3+g3+h3-1, e3*f3, e3*g3, e3*h3, f3*g3, g3*h3, e4+f4+g4+h4-1, e4*f4, e4*g4, e4*h4, f4*g4, g4*h4,i1+j1+k1+l1-1, i1*j1, i1*k1, i1*l1,j1*k1, j1*l1, k1*l1, i2+j2+k2+l2-1, i2*j2, i2*k2, i2*l2,j2*k2, j2*l2, k2*l2, i3+j3+k3+l3-1, i3*j3, i3*k3, i3*l3,j3*k3, j3*l3, k3*l3, i4+j4+k4+l4-1, i4*j4, i4*k4, i4*l4,j4*k4, j4*l4, k4*l4, m1+n1+q1+p1-1, m1*n1, m1*q1, m1*p1, n1*q1, n1*p1, q1*p1, m2+n2+q2+p2-1, m2*n2, m2*q2, m2*p2, n2*q2, n2*p2, q2*p2,m3+n3+q3+p3-1, m3*n3, m3*q3, m3*p3, n3*q3, n3*p3, q3*p3,m4+n4+q4+p4-1, m4*n4, m4*q4, m4*p4, n4*q4, n4*p4, q4*p4,a1+e1+i1+m1-1, a1*e1, a1*i1, a1*m1, e1*i1, e1*m1, a2+e2+i2+m2-1, a2*e2, a2*i2, a2*m2, e2*i2, e2*m2, a3+e3+i3+m3-1, a3*e3, a3*i3, a3*m3, e3*i3, e3*m3, a4+e4+i4+m4-1, a4*e4, a4*i4, a4*m4, e4*i4, e4*m4, b1+f1+j1+n1-1, b1*f1, b1*j1, b1*n1, f1*j1, f1*n1, j1*n1, b2+f2+j2+n2-1, b2*f2, b2*j2, b2*n2, f2*j2, f2*n2, j2*n2, b3+f3+j3+n3-1, b3*f3, b3*j3, b3*n3, f3*j3, f3*n3, j3*n3, b4+f4+j4+n4-1, b4*f4, b4*j4, b4*n4, f4*j4, f4*n4, j4*n4, c1+g1+k1+q1-1, c1*g1, c1*k1, c1*q1, g1*k1, g1*q1, k1*q1,  c2+g2+k2+q2-1, c2*g2, c2*k2, c2*q2, g2*k2, g2*q2, k2*q2,  c3+g3+k3+q3-1, c3*g3, c3*k3, c3*q3, g3*k3, g3*q3, k3*q3,  c4+g4+k4+q4-1, c4*g4, c4*k4, c4*q4, g4*k4, g4*q4, k4*q4, d1+h1+l1+p1-1, d1*h1, d1*l1, d1*p1, h1*l1, h1*p1, l1*p1,d2+h2+l2+p2-1, d2*h2, d2*l2, d2*p2, h2*l2, h2*p2, l2*p2,d3+h3+l3+p3-1, d3*h3, d3*l3, d3*p3, h3*l3, h3*p3, l3*p3,d4+h4+l4+p4-1, d4*h4, d4*l4, d4*p4, h4*l4, h4*p4, l4*p4, a1+b1+e1+f1-1, a1*f1, a1*e1, a1*b1, b1*e1, b1*f1, e1*f1, a2+b2+e2+f2-1, a2*b2, a2*e2, a2*f2,b2*e2, b2*f2, e2*f2, a3+b3+e3+f3-1, a3*b3, a3*e3, a3*f3,b3*e3, b3*f3, e3*f3, a4+b4+e4+f4-1, a4*b4, a4*e4, a4*f4,b4*e4,b4*f4, e4*f4,c1+d1+g1+h1-1, c1*d1, c1*g1, c1*h1, d1*h1, g1*h1, d1*g1,c2+d2+g2+h2-1, c2*h2, d2*g2, c3+d3+g3+h3-1, c3*d3, c3*g3, c3*h3, d3*g3, d3*h3, g3*h3, c4+d4+g4+h4-1, c4*d4, c4*g4, c4*h4, d4*g4, d4*h4, g4*h4, i1+j1+m1+n1-1, i1*j1, i1*m1, i1*n1, j1*m1, j1*n1, m1*n1, i2+j2+m2+n2-1, i2*j2, i2*m2, i2*n2, j2*m2, j2*n2, m2*n2, i3+j3+m3+n3-1, i3*j3, i3*m3, i3*n3, j3*m3,j3*n3, m3*n3, i4+j4+m4+n4-1, i4*j4, i4*m4, i4*n4, j4*m4,j4*n4, m4*n4, k1+l1+q1+p1-1, k1*l1, k1*q1, k1*p1, l1*q1, l1*p1, q1*p1, k2+l2+q2+p2-1, k2*l2, k2*q2, k2*p2, l2*q2,l2*p2, p2*q2, k3+l3+q3+p3-1, k3*l3, k3*q3, k3*p3, l3*q3, l3*p3, q3*p3, k4+l4+q4+p4-1, k4*l4, k4*q4, k4*p4, l4*q4, l4*p4, q4*p4}
  II00 = ideal {d1, d2, d3, d4-1, e1, e2, e3, e4-1, g1, g2-1, g3, g4, j1, j2, j3-1, j4, l1-1, l2, l3, l4, m1-1, m2, m3, m4}
  correctSolution = ideal matrix {{p3*p4, p2*p4, p2*p3, p1+p2+p3+p4+1, q4*p4, q3*p3, q3*q4, q2*p3+q2*p4+q2+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, q2*p2, q2*q4, q2*q3, q1+q2+q3+q4+1, n4*p4, n4*q4, n3*p3, n3*q4+n3*p4+n3+n4*q3+n4*p3+n4+q3*p4+q3+q4*p3+q4+p3+p4+1, n3*q3, n3*q2*p4+n3*q2+n4*q3*p2+n4*q3+n4*p2+n4*p3+n4+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, n3*n4, n2*p3+n2*p4+n2+n3*p2+n3*p4+n3+n4*p2+n4*p3+n4+p2+p3+p4+1, n2*p2, n2*q4+n2*p4+n2+n4*q2+n4*p2+n4+q2*p4+q2+q4*p2+q4+p2+p4+1, n2*q3+n2*p4+n3*q2+n3*p4+n4*p2+n4*p3+n4+q2*p4+q3*p4+q4*p2+q4*p3+q4+p2+p3+1, n2*q2, n2*n4, n2*n3, n1+n2+n3+n4+1, m4+n4+q4+p4+1, m3+n3+q3+p3+1, m2+n2+q2+p2+1, m1+n2+n3+n4+q2+q3+q4+p2+p3+p4, l4*p4, l4*q4, l4*n3+l4*n4*q3+l4*n4*p3+l4*n4+l4*q3+l4*p3+l4, l4*n2+l4*n4*q2+l4*n4*p2+l4*n4+l4*q2+l4*p2+l4, l3*p3, l3*q4+l3*p4+l3+l4*q3+l4*p3+l4+q3*p4+q3+q4*p3+q4+p3+p4+1, l3*q3, l3*q2*p4+l3*q2+l4*q3*p2+l4*q3+l4*p2+l4*p3+l4+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, l3*n4+l4*n4*q3+l4*n4*p3+l4*n4+n4*q3+n4*p3+n4, l3*n2+l3*n3*q2+l3*n3*p2+l3*n3+l3*q2+l3*p2+l3, l3*l4, l2*p3+l2*p4+l2+l3*p2+l3*p4+l3+l4*p2+l4*p3+l4+p2+p3+p4+1, l2*p2, l2*q4+l2*p4+l2+l4*q2+l4*p2+l4+q2*p4+q2+q4*p2+q4+p2+p4+1, l2*q3+l2*p4+l3*q2+l3*p4+l4*p2+l4*p3+l4+q2*p4+q3*p4+q4*p2+q4*p3+q4+p2+p3+1, l2*q2, l2*n4+l4*n4*q2+l4*n4*p2+l4*n4+n4*q2+n4*p2+n4, l2*n3+l3*n3*q2+l3*n3*p2+l3*n3+n3*q2+n3*p2+n3, l2*l4, l2*l3, l1+l2+l3+l4+1, k4+l4+q4+p4+1, k3+l3+q3+p3+1, k2+l2+q2+p2+1, k1+l2+l3+l4+q2+q3+q4+p2+p3+p4, j4*q4+j4*p4+j4, j4*q3*p4+j4*q3, j4*q3*p2, j4*q2*p4+j4*q2, j4*n4, j4*l4, j3*p4+j4*q3+q3*p4, j3*q4+j4*p3+q4*p3, j3*q3+j3*p3+j3, j3*n3, j3*n2+j3*n4*q2+j3*n4*p2+j3*n4+j3*q2+j3*p2+j3+j4*n2+j4*n3*q2+j4*n3*p2+j4*n3+j4*q2+j4*p2+j4+n2+n3*q2+n3*p2+n3+n4*q2+n4*p2+n4+q2+p2+1, j3*l3, j3*l2+j3*l4*q2+j3*l4*p2+j3*l4+j3*q2+j3*p2+j3+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q2+j4*p2+j4+l2+l3*q2+l3*p2+l3+l4*q2+l4*p2+l4+q2+p2+1, j3*j4, j2*p4+j4*q2+q2*p4, j2*p3+j3*q2+q2*p4+q2+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, j2*q4+j4*p2+q4*p2, j2*q3+j3*p2+q3*p2, j2*q2+j2*p2+j2, j2*n3+j2*n4+j2+j3*n4*q2+j3*n4*p2+j3*q2+j3*p2+j4*n3*q2+j4*n3*p2+j4*q2+j4*p2+n3*q2+n3*p2+n4*q2+n4*p2+q2+p2, j2*n2, j2*l3+j2*l4+j2+j3*l4*q2+j3*l4*p2+j3*q2+j3*p2+j4*l3*q2+j4*l3*p2+j4*q2+j4*p2+l3*q2+l3*p2+l4*q2+l4*p2+q2+p2, j2*l2, j2*j4, j2*j3, j1+j2+j3+j4+1, i4+j4+q4+p4, i3+j3+q3+p3, i2+j2+q2+p2, i1+j2+j3+j4+q2+q3+q4+p2+p3+p4+1, h4*p4, h4*n3*q2+h4*n4*q3*p2+h4*n4*q3+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p2+h4*p3+h4, h4*l4, h4*l3*q2+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p2+h4*p3+h4, h4*j4*q3, h4*j4*q2, h3*p3, h3*q4+h4*l3+h4*q3+h4*p3+h4+l3*p4+l3+l4*q3+l4*p3+l4+q3*p4+q3+p3+p4+1, h3*q2*p4+h3*q2+h3*q3*p2+h3*q3*p4+h3*q3+h3*p2+h3*p4+h3+h4*l3*p2+h4*l3+h4*q3*p2+h4*q3+h4*p2+h4*p3+h4+l3*p2+l3*p4+l3+l4*q3*p2+l4*q3+l4*p2+l4*p3+l4+q3*p2+q3*p4+q3+p2+p3+p4+1, h3*n4*q2+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*n4, h3*n3*p4+h3*n3+h3*n4*q3+h3*n4+h3*q3*p4+h3*q3+h3*p4+h3+h4*l3*n3+h4*l3+h4*n3+h4*q3+h4*p3+h4+l3*n3*p4+l3*n3+l3*p4+l3+l4*n4*q3+l4*n4*p3+l4*n4+n3*p4+n3+q3*p4+q3+p3+p4+1, h3*n3*p2+h3*n4*q3*p2+h3*n4*p2+h3*q3*p2+h3*p2+h4*l3*n3*p2+h4*l3*p2+h4*n3*p2+h4*q3*p2+h4*p2+l3*n3*p2+l3*p2+l4*n4*q3*p2+l4*n4*p2+n3*p2+q3*p2+p2, h3*n2*p4+h3*n2+h3*n4*q3*p2+h3*n4*q3+h3*q3*p2+h3*q3*p4+h3*q3+h4*l3*n3*p2+h4*l3*n3+h4*l3*p2+h4*l3+h4*n3*p2+h4*n3+h4*q3*p2+h4*q3+h4*p2+h4*p3+h4+l3*n3*p2+l3*n3*p4+l3*n3+l3*p2+l3*p4+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+n3*p2+n3*p4+n3+q3*p2+q3*p4+q3+p2+p3+p4+1, h3*l4+h3*p4+h3+h4*l3+h4*p3+h4+l3*p4+l3+l4*p3+l4+p3+p4+1, h3*l3, h3*l2*p4+h3*l2+h4*l3*p2+h4*l3+h4*p2+h4*p3+h4+l3*p2+l3*p4+l3+l4*p2+l4*p3+l4+p2+p3+p4+1, h3*j4*p4+h3*j4+h4*j4*l3+h4*j4*p3+h4*j4+j4*l3*p4+j4*l3+j4*p3+j4*p4+j4, h3*j4*p2+h4*j4*l3*p2+h4*j4*p2+j4*l3*p2+j4*p2, h3*j3*q2, h3*h4, h2*p3+h2*p4+h2+h3*p2+h3*p4+h3+h4*p2+h4*p3+h4+p2+p3+p4+1, h2*p2, h2*q4+h4*l2+h4*q2+h4*p2+h4+l2*p4+l2+l4*q2+l4*p2+l4+q2*p4+q2+p2+p4+1, h2*q3+h3*l2+h3*q2+h3*p2+h3+l2*p4+l3*q2+l3*p4+l4*p2+l4*p3+l4+q2*p4+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+1, h2*n3*p4+h2*n3+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*n4+h3*q3*p2+h3*q3*p4+h3*q3+h3*p2+h3*p4+h3+h4*l3*n3*p2+h4*l3*n3+h4*l3*p2+h4*l3+h4*q3*p2+h4*q3+h4*p2+h4*p3+h4+l3*n3*p2+l3*n3*p4+l3*n3+l3*p2+l3*p4+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+q3*p2+q3*p4+q3+p2+p3+p4+1, h2*n2+h2*n3*q2+h2*n3+h2*n4*q2+h2*n4+h2*q2+h2+h3*l2*n2+h3*l2+h3*n2+h3*n4*q3*p2+h3*n4*q3+h3*q2+h3*p2+h3+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*n2+h4*n4*p2+h4*n4*p3+h4*n4+h4*q2+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+l2*n2+l2+l3*n3*q2+l3*n3*p2+l3*n3+l4*n4*q2+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4+n2+n4*q3*p2+n4*q3+q2+p2+1, h2*l4+h2*p4+h2+h4*l2+h4*p2+h4+l2*p4+l2+l4*p2+l4+p2+p4+1, h2*l3+h2*p4+h3*l2+h3*p4+h4*p2+h4*p3+h4+l2*p4+l3*p4+l4*p2+l4*p3+l4+p2+p3+1, h2*l2, h2*j4*p4+h2*j4+h4*j4*l2+h4*j4*p2+h4*j4+j4*l2*p4+j4*l2+j4*p2+j4*p4+j4, h2*j2+h2*j3*q2+h2*j4*q2+h2*q2+h3*j2*p2+h3*j2+h3*j4*q2+h3*q2+h4*j2*p2+h4*j2+h4*j3*q2+h4*q2+j2*p2+j2+j3*q2+j4*q2+q2, h2*h4, h2*h3, h1+h2+h3+h4+1, g4*q4, g4*n3*p4+g4*n3+g4*n4*q3+g4*n4*p3+g4*n4+g4*q3*p4+g4*q3+g4*p3+g4*p4+g4, g4*n3*p2+g4*n4*q3*p2+g4*n4*p2+g4*q3*p2+g4*p2, g4*n2*p4+g4*n2+g4*n4*q2+g4*n4*p2+g4*n4+g4*q2*p4+g4*q2+g4*p2+g4*p4+g4, g4*l4+g4*p4+g4, g4*l3*p4+g4*l3, g4*l3*p2, g4*l2*p4+g4*l2, g4*j4+g4*l2+g4*l3*q2+g4*n2+g4*n3*q2+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p3+g4*p4+h2*j4+h2*n3+h3*j4*l2+h3*l2+h3*n2+h3*n4*p2+h3*n4+h3*p2+h3+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*l3*p2+h4*l3+h4*n3*p2+h4*n3+h4*p2+h4*p3+h4+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q3+j4*p3+l3*p2+l3+l4*p2+l4*p3+l4+n3*q2+n3*p2+n3+n4*q3*p2+n4*q3+n4*p2+n4*p3+n4+q3*p2+q3+q4*p2+q4*p3+q4+p4, g4*j3+g4*l2+g4*l3*q2+g4*l3+g4*n2+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*n4+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p4+g4+h2*j3+h2*n4+h3*j3*p2+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*n2+h3*n3*q2+h3*n3+h3*n4+h3*q2+h3*q3*p2+h3*q3+h3+h4*j3*q2+h4*j3*p2+h4*j4*l2+h4*j4*l3+h4*j4+h4*l2+h4*l3*n3*p2+h4*l3+h4*n3*p2+h4*n4*q2+h4*n4*q3*p2+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+h4*p2+h4*p3+j3*q2+j3*p2+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4+l2+l3*n3*p2+l3*q2+l3+l4*n4*q3*p2+l4*n4*p2+l4*q2+l4*p2+l4+n3*p2+n4*q2+n4*q3*p2+q2+q3*p2+q3*p4+q3+1, g4*j2+g4*l3*q2+g4*n3*q2+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*n4+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3*q2+h2*j4*q2+h2*n3*q2+h2*n4*q2+h3*j2+h3*j4*q2+h3*n4*q3*p2+h3*n4*q3+h3*n4+h4*j3*q2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*l3*p2+h4*n4*q2+h4*n4*q3+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+h4+j3*q2+j3*p2+j4*l3*p2+j4*p2+l3*q2+l3*p2+l4*q3+l4*p3+l4+n4*q2+n4*q3+n4*p2+n4*p3+n4+q2*p4+p2, g4*h4, g3*p4+g4*l3+l3*p4, g3*q3, g3*n3*q2+g3*n4*p2+g3*n4*p3+g3*n4+g3*q4*p2+g3*q4*p3+g3*q4+g3*p2+g3*p3+g3+g4*l3*n3*q2+g4*l3+l3*n3*q2+l3*p4+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+l4*q3*p2+l4*q3+l4*p2+l4*p3+l4+n4*q3*p2+n4*q3+n4*p2+n4*p3+n4+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, g3*l4+g4*p3+l4*p3, g3*l3+g3*p3+g3, g3*j4+g3*l2+g3*n2+g3*n3*p2+g3*n4*q2+g3*n4+g3*p2+g4*l3*n3*q2+g4*l3*q2+g4*l3+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p4+g4+h2*j4+h2*n3+h3*j4*l2+h3*j4+h3*n3*q2+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*j4+h4*l2+h4*l3*n3*p2+h4*l3*p2+h4*n2+h4*n3*p2+h4*n3+h4*n4*q2+h4*n4*q3*p2+h4*n4+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4+l3*n3*q2+l3*n3*p2+l3*q2+l3+l4*n4*q3+l4*n4*p3+l4*n4+l4*q2+l4*p3+n3*q2+n4*q3+n4*p3+n4+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, g3*j3+g3*l2+g3*n2+g3*n3*p2+g3*n3+g3*n4*q2+g3*p2+g3+g4*l3*n3*q2+g4*l3*q2+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3+h2*n4+h3*j3*p2+h3*j3+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*l2+h3*n4*p2+h3*n4+h3*q2+h3*q3*p2+h3*q3+h3*p2+h3+h4*j3*q2+h4*j3*p2+h4*j3+h4*j4*l2+h4*j4*l3+h4*j4+h4*n2+h4*n3*p2+h4*n3+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+j3*q2+j3*p2+j3+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4*q3+j4*p3+j4+l2+l3*n3*q2+l3*p2+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+n4*q2+n4*p2+n4+q2+q3*p2+q3+p2+p3+1, g3*j2+g3*n3*p2+g3*n4*q2+g4*l3*n3*q2+g4*l3*q2+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3*q2+h2*j4*q2+h2*n3*q2+h2*n4*q2+h3*j4*q2+h3*n3*q2+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*n4+h4*j2+h4*j3*q2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*l3*n3*p2+h4*l3*p2+h4*n4*q3*p2+h4*n4*q3+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+h4+j4*l3*p2+j4*q2+l3*n3*q2+l3*n3*p2+l3*q2+l3*p2+l4*n4*q3+l4*n4*p3+l4*n4+n3*q2+n4*q3*p2+n4*p2+q2*p4+q2+q3*p2+q3*p4+q3+q4*p2+q4*p3+q4+p2+p3+p4+1, g3*h3, g3*h2+g3*h4*l2+g3*h4*p2+g3*h4+g3*l2+g3*p2+g3+g4*h2+g4*h3*l2+g4*h3*p2+g4*h3+g4*l2+g4*p2+g4+h2+h3*l2+h3*p2+h3+h4*l2+h4*p2+h4+l2+p2+1, g3*g4, g2*p4+g4*l2+l2*p4, g2*p3+g3*l2+l2*p4+l2+l3*p2+l3*p4+l3+l4*p2+l4*p3+l4+p2+p3+p4+1, g2*q3+g2*q4+g2+g3*q2+g3*q4+g3+g4*q2+g4*q3+g4+q2+q3+q4+1, g2*q2, g2*n2+g2*n3*p2+g2*n3+g2*n4*p2+g2*n4+g2*p2+g2+g3*l2*n2+g3*l2+g3*n4*q2+g3*n4*p2+g3*n4+g4*l2*n2+g4*l2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3+g4*n4+g4*q3*p2+g4*p2+l2*n2+l2+l3*n3*q2+l3*n3*p2+l3*n3+l4*n4*q3*p2+l4*n4*q3+n3*q2+n3*p2+n3+n4*q2+n4*p2+n4, g2*l4+g4*p2+l4*p2, g2*l3+g3*p2+l3*p2, g2*l2+g2*p2+g2, g2*j4+g2*n3+g3*l2*n2+g3*l2+g3*n4*q2+g3*n4+g3*p2+g4*l2*n2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p2+g4*n4+h3*j4*l2+h3*l2*n2+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*j4+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*l3+h4*n3+h4*n4*q2+h4*n4*q3+h4*n4+h4*p2+h4*p3+h4+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q2+j4*q3+j4*p2+j4*p3+j4+l3*q2+l3+l4*n4*q2+l4*n4*p2+l4*n4+l4*q3+l4*p2+n4*q3+n4*p2+q2*p4+q3*p2+q3+q4*p2+q4*p3+q4+p4, g2*j3+g2*n4+g3*l2*n2+g3*n4*q2+g3*n4+g4*l2*n2+g4*l2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p2+g4*n4+g4*p2+h3*j3*p2+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*l2*n2+h3*n3*q2+h3*n3+h3*n4*p2+h3*q2+h3*q3*p2+h3*q3+h3+h4*j3*q2+h4*j3*p2+h4*j3+h4*j4*l2+h4*j4*l3+h4*j4+h4*l2*n2+h4*l2+h4*l3*n3+h4*l3*p2+h4*n3+h4*n4*q3*p2+h4*n4*q3+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+h4+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4*q3+j4*p3+j4+l2+l3*n3*p2+l3*q2+l3+l4*n4*q2+l4*n4*q3*p2+l4*n4+n3*p2+n4*q3+n4*p2+q2*p4+q3*p4+q4*p2+q4*p3+q4+p2+p4, g2*j2+g2*n3*p2+g2*n4*p2+g2*p2+g3*n4*p2+g3*p2+g4*n4*q3*p2+g4*n4*p2+g4*q3*p2+h3*j2*p2+h3*n4*p2+h4*j2*p2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*n3*p2+j2*p2+j3*p2+j4*l3*p2, g2*h3+g2*h4+g2+g3*h4*l2+g3*h4*p2+g3*l2+g3*p2+g4*h3*l2+g4*h3*p2+g4*l2+g4*p2+h3*l2+h3*p2+h4*l2+h4*p2+l2+p2, g2*h2, g2*g4, g2*g3, g1+g2+g3+g4+1, f4+g4*l2+g4*l3*q2+g4*n2+g4*n3*q2+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*n4+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p3+g4*p4+g4+h2*j4+h2*n3+h3*j4*l2+h3*l2+h3*n2+h3*n4*p2+h3*n4+h3*p2+h3+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*j4+h4*l3*p2+h4*l3+h4*n3*p2+h4*n3+h4*n4+h4*p2+h4*p3+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q3+j4*p3+j4+l3*p2+l3+l4*p2+l4*p3+l4+n3*q2+n3*p2+n3+n4*q3*p2+n4*q3+n4*p2+n4*p3+q3*p2+q3+q4*p2+q4*p3+q4+p4+1, f3+g3*l2+g3*n2+g3*n3*p2+g3*n4*q2+g3*p2+g4*l3*n3*q2+g4*l3*q2+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3+h2*n4+h3*j3*p2+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*l2+h3*n3+h3*n4*p2+h3*n4+h3*q2+h3*q3*p2+h3*q3+h3*p2+h4*j3*q2+h4*j3*p2+h4*j3+h4*j4*l2+h4*j4*l3+h4*j4+h4*n2+h4*n3*p2+h4*n3+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+j3*q2+j3*p2+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4*q3+j4*p3+j4+l2+l3*n3*q2+l3*p2+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+n3+n4*q2+n4*p2+n4+q2+q3*p2+q3+p2+p3, f2+g2*n3+g2*n4+g3*l2*n2+g3*l2+g3*n4*q2+g3*n4+g3*p2+g4*l2*n2+g4*l2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p2+g4*n4+g4*p2+h2*j3*q2+h2*j4*q2+h2*n3*q2+h2*n3+h2*n4*q2+h2*n4+h3*j2+h3*j4*q2+h3*l2*n2+h3*l2+h3*n2+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*p2+h3+h4*j2+h4*j3*q2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*n2+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+j3*q2+j3*p2+j4*l3*p2+j4*q2+l4*n4*q2+l4*n4*p2+l4*n4+n3*q2+n3*p2+n3+n4*q2+n4*q3*p2+n4*q3+n4*p2+n4+p2, f1+g2*n3+g2*n4+g3*l2*n2+g3*n2+g3*n3*p2+g3*n4+g4*l2*n2+g4*l3*n3+g4*n2+g4*n3+g4*n4*p2+g4*n4*p3+h2*j3*q2+h2*j3+h2*j4*q2+h2*j4+h2*n3*q2+h2*n4*q2+h3*j2+h3*j3*p2+h3*j4*q3+h3*j4+h3*l2*n2+h3*l2+h3*n3+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*q2+h3*q3*p2+h3*q3+h3*p2+h4*j2+h4*j3+h4*j4*p2+h4*j4*p3+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*l3*p2+h4*l3+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*q2+h4*q3*p2+h4*q3+h4*p2+l2+l3*n3*q2+l4*n4*q2+l4*n4*q3*p2+l4*n4*q3+l4*n4*p3+l4*p2+l4*p3+l4+n3+n4*p2+n4*p3+q2+q4*p2+q4*p3+q4+p3+p4, e4+g4*l2+g4*l3*q2+g4*n2+g4*n3*q2+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*n4+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p3+g4*p4+h2*j4+h2*n3+h3*j4*l2+h3*l2+h3*n2+h3*n4*p2+h3*n4+h3*p2+h3+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*j4+h4*l3*p2+h4*l3+h4*n3*p2+h4*n3+h4*n4+h4*p2+h4*p3+h4+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q3+j4*p3+j4+l3*p2+l3+l4*p2+l4*p3+l4+n3*q2+n3*p2+n3+n4*q3*p2+n4*q3+n4*p2+n4*p3+q3*p2+q3+q4*p2+q4*p3+q4+p4, e3+g3*l2+g3*n2+g3*n3*p2+g3*n4*q2+g3*p2+g3+g4*l3*n3*q2+g4*l3*q2+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3+h2*n4+h3*j3*p2+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*l2+h3*n3+h3*n4*p2+h3*n4+h3*q2+h3*q3*p2+h3*q3+h3*p2+h3+h4*j3*q2+h4*j3*p2+h4*j3+h4*j4*l2+h4*j4*l3+h4*j4+h4*n2+h4*n3*p2+h4*n3+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+j3*q2+j3*p2+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4*q3+j4*p3+j4+l2+l3*n3*q2+l3*p2+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+n3+n4*q2+n4*p2+n4+q2+q3*p2+q3+p2+p3+1, e2+g2*n3+g2*n4+g2+g3*l2*n2+g3*l2+g3*n4*q2+g3*n4+g3*p2+g4*l2*n2+g4*l2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p2+g4*n4+g4*p2+h2*j3*q2+h2*j4*q2+h2*n3*q2+h2*n3+h2*n4*q2+h2*n4+h2+h3*j2+h3*j4*q2+h3*l2*n2+h3*l2+h3*n2+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*p2+h3+h4*j2+h4*j3*q2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*n2+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+j3*q2+j3*p2+j4*l3*p2+j4*q2+l4*n4*q2+l4*n4*p2+l4*n4+n3*q2+n3*p2+n3+n4*q2+n4*q3*p2+n4*q3+n4*p2+n4+p2+1, e1+g2*n3+g2*n4+g2+g3*l2*n2+g3*n2+g3*n3*p2+g3*n4+g3+g4*l2*n2+g4*l3*n3+g4*n2+g4*n3+g4*n4*p2+g4*n4*p3+g4+h2*j3*q2+h2*j3+h2*j4*q2+h2*j4+h2*n3*q2+h2*n4*q2+h2+h3*j2+h3*j3*p2+h3*j4*q3+h3*j4+h3*l2*n2+h3*l2+h3*n3+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*q2+h3*q3*p2+h3*q3+h3*p2+h3+h4*j2+h4*j3+h4*j4*p2+h4*j4*p3+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*l3*p2+h4*l3+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*q2+h4*q3*p2+h4*q3+h4*p2+h4+l2+l3*n3*q2+l4*n4*q2+l4*n4*q3*p2+l4*n4*q3+l4*n4*p3+l4*p2+l4*p3+l4+n3+n4*p2+n4*p3+q2+q4*p2+q4*p3+q4+p3+p4+1, d4+h4+l4+p4+1, d3+h3+l3+p3+1, d2+h2+l2+p2+1, d1+h2+h3+h4+l2+l3+l4+p2+p3+p4, c4+g4+l4+p4, c3+g3+l3+p3, c2+g2+l2+p2, c1+g2+g3+g4+l2+l3+l4+p2+p3+p4+1, b4+g4*l2+g4*l3*q2+g4*n2+g4*n3*q2+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*n4+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p3+g4*p4+g4+h2*j4+h2*n3+h3*j4*l2+h3*l2+h3*n2+h3*n4*p2+h3*n4+h3*p2+h3+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*j4+h4*l3*p2+h4*l3+h4*n3*p2+h4*n3+h4*n4+h4*p2+h4*p3+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q3+j4*p3+l3*p2+l3+l4*p2+l4*p3+l4+n3*q2+n3*p2+n3+n4*q3*p2+n4*q3+n4*p2+n4*p3+n4+q3*p2+q3+q4*p2+q4*p3+q4+p4, b3+g3*l2+g3*n2+g3*n3*p2+g3*n4*q2+g3*p2+g4*l3*n3*q2+g4*l3*q2+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3+h2*n4+h3*j3*p2+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*l2+h3*n3+h3*n4*p2+h3*n4+h3*q2+h3*q3*p2+h3*q3+h3*p2+h4*j3*q2+h4*j3*p2+h4*j3+h4*j4*l2+h4*j4*l3+h4*j4+h4*n2+h4*n3*p2+h4*n3+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+j3*q2+j3*p2+j3+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4*q3+j4*p3+j4+l2+l3*n3*q2+l3*p2+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+n4*q2+n4*p2+n4+q2+q3*p2+q3+p2+p3+1, b2+g2*n3+g2*n4+g3*l2*n2+g3*l2+g3*n4*q2+g3*n4+g3*p2+g4*l2*n2+g4*l2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p2+g4*n4+g4*p2+h2*j3*q2+h2*j4*q2+h2*n3*q2+h2*n3+h2*n4*q2+h2*n4+h3*j2+h3*j4*q2+h3*l2*n2+h3*l2+h3*n2+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*p2+h3+h4*j2+h4*j3*q2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*n2+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+j2+j3*q2+j3*p2+j4*l3*p2+j4*q2+l4*n4*q2+l4*n4*p2+l4*n4+n2+n3*q2+n3*p2+n3+n4*q2+n4*q3*p2+n4*q3+n4*p2+n4+p2+1, b1+g2*n3+g2*n4+g3*l2*n2+g3*n2+g3*n3*p2+g3*n4+g4*l2*n2+g4*l3*n3+g4*n2+g4*n3+g4*n4*p2+g4*n4*p3+h2*j3*q2+h2*j3+h2*j4*q2+h2*j4+h2*n3*q2+h2*n4*q2+h3*j2+h3*j3*p2+h3*j4*q3+h3*j4+h3*l2*n2+h3*l2+h3*n3+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*q2+h3*q3*p2+h3*q3+h3*p2+h4*j2+h4*j3+h4*j4*p2+h4*j4*p3+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*l3*p2+h4*l3+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*q2+h4*q3*p2+h4*q3+h4*p2+j2+j3+j4+l2+l3*n3*q2+l4*n4*q2+l4*n4*q3*p2+l4*n4*q3+l4*n4*p3+l4*p2+l4*p3+l4+n2+n4*p2+n4*p3+n4+q2+q4*p2+q4*p3+q4+p3+p4+1, a4+g4*l2+g4*l3*q2+g4*n2+g4*n3*q2+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p3+g4*n4+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p3+g4*p4+h2*j4+h2*n3+h3*j4*l2+h3*l2+h3*n2+h3*n4*p2+h3*n4+h3*p2+h3+h4*j4*l2+h4*j4*l3*p2+h4*j4*l3+h4*j4*p3+h4*j4+h4*l3*p2+h4*l3+h4*n3*p2+h4*n3+h4*n4+h4*p2+h4*p3+h4+j4*l2+j4*l3*q2+j4*l3*p2+j4*l3+j4*q3+j4*p3+l3*p2+l3+l4*p2+l4*p3+l4+n3*q2+n3*p2+n3+n4*q3*p2+n4*q3+n4*p2+n4*p3+n4+q3*p2+q3+q4*p2+q4*p3+q4+p4, a3+g3*l2+g3*n2+g3*n3*p2+g3*n4*q2+g3*p2+g3+g4*l3*n3*q2+g4*l3*q2+g4*q2*p4+g4*q2+g4*q3*p2+g4*q3*p4+g4*q3+g4*p2+g4*p3+g4*p4+g4+h2*j3+h2*n4+h3*j3*p2+h3*j4*l2+h3*j4*q2+h3*j4*q3+h3*j4+h3*l2+h3*n3+h3*n4*p2+h3*n4+h3*q2+h3*q3*p2+h3*q3+h3*p2+h3+h4*j3*q2+h4*j3*p2+h4*j3+h4*j4*l2+h4*j4*l3+h4*j4+h4*n2+h4*n3*p2+h4*n3+h4*q2+h4*q4*p2+h4*q4*p3+h4*q4+j3*q2+j3*p2+j3+j4*l2+j4*l3*q2+j4*l3+j4*q2+j4*q3+j4*p3+j4+l2+l3*n3*q2+l3*p2+l3+l4*n4*q3*p2+l4*n4*q3+l4*n4*p2+l4*n4*p3+l4*n4+n4*q2+n4*p2+n4+q2+q3*p2+q3+p2+p3+1, a2+g2*n3+g2*n4+g2+g3*l2*n2+g3*l2+g3*n4*q2+g3*n4+g3*p2+g4*l2*n2+g4*l2+g4*l3*n3*q2+g4*l3*n3+g4*n3*q2+g4*n3+g4*n4*q2+g4*n4*q3*p2+g4*n4*q3+g4*n4*p2+g4*n4+g4*p2+h2*j3*q2+h2*j4*q2+h2*n3*q2+h2*n3+h2*n4*q2+h2*n4+h2+h3*j2+h3*j4*q2+h3*l2*n2+h3*l2+h3*n2+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*p2+h3+h4*j2+h4*j3*q2+h4*j3*p2+h4*j4*l3*p2+h4*j4*p2+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*n2+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*n4+h4*q3*p2+h4*q3+h4*q4*p2+h4*q4*p3+h4*q4+h4*p3+j2+j3*q2+j3*p2+j4*l3*p2+j4*q2+l4*n4*q2+l4*n4*p2+l4*n4+n2+n3*q2+n3*p2+n3+n4*q2+n4*q3*p2+n4*q3+n4*p2+n4+p2+1, a1+g2*n3+g2*n4+g2+g3*l2*n2+g3*n2+g3*n3*p2+g3*n4+g3+g4*l2*n2+g4*l3*n3+g4*n2+g4*n3+g4*n4*p2+g4*n4*p3+g4+h2*j3*q2+h2*j3+h2*j4*q2+h2*j4+h2*n3*q2+h2*n4*q2+h2+h3*j2+h3*j3*p2+h3*j4*q3+h3*j4+h3*l2*n2+h3*l2+h3*n3+h3*n4*q3*p2+h3*n4*q3+h3*n4*p2+h3*q2+h3*q3*p2+h3*q3+h3*p2+h3+h4*j2+h4*j3+h4*j4*p2+h4*j4*p3+h4*l2*n2+h4*l2+h4*l3*n3*p2+h4*l3*n3+h4*l3*p2+h4*l3+h4*n3*p2+h4*n4*p2+h4*n4*p3+h4*q2+h4*q3*p2+h4*q3+h4*p2+h4+j2+j3+j4+l2+l3*n3*q2+l4*n4*q2+l4*n4*q3*p2+l4*n4*q3+l4*n4*p3+l4*p2+l4*p3+l4+n2+n4*p2+n4*p3+n4+q2+q4*p2+q4*p3+q4+p3+p4+1}}
  assert (correctSolution == gbBoolean II0)
  correctSolution = ideal matrix {{p4, p3, p2+1, p1, q4, q3+1, q2, q1, n4+1, n3, n2, n1, m4, m3, m2,
    m1+1, l4, l3, l2, l1+1, k4+1, k3, k2, k1, j4, j3+1, j2, j1, i4, i3, i2+1, i1, h4, h3+1, h2, h1, g4, g3, g2+1, g1, f4, f3, f2, f1+1, e4+1, e3, e2, e1, d4+1, d3, d2, d1, c4, c3, c2, c1+1, b4, b3, b2+1, b1, a4, a3+1, a2, a1}}
  assert (correctSolution == gbBoolean (II0+II00))
///

TEST ///
  R = ZZ/2[ vars(1..20), MonomialOrder=>Lex]
  QR = R / ideal apply(gens R, x -> x^2 + x)
  II3 = ideal (c*k*r + 1, b*d*h*i*n + b*h*i*n + b*d*h + b*d*i + b*i*n + d*n + b, g*h*l*o*r + g*o, j*l*m + d*m*t + l*m*t + l*t, e*k*t*u + g*k*t*u + e*g*k + e*g*u + g*k + u, m*n*q*r + k*n + n*q + m*r + 1, b*e*g*o + e*g*o*s + b*g*o + e*g*o + b*o*s + e*o*s + e*g, e*g*k*q + g*k*q*t + g*k*q + g*t + k*t, j*m*t*u + f*j*t, o*q*t*u + o*t*u, p*s*u + q*r + r*s + q + u, b*s, b*f*n*s + f*n*s + n*s*t + f*n + f, d*p + d*t, g*l*q*t + q*t, c*d*e*p*q, d*q*r*t + o*q*r + d*q + o*r + r*t + o, d*h*m*n*p + h*m*n*p, f*k*o*s*t + f*k*o*s + f*o*s*t + k*o*s*t + f*k*o + f*k*s + f*k*t + f*k + o*t + f, k*q*t + h*q + h + 1)
  correctSolution = ideal gens gb( II3, Algorithm=>Sugarless)
  G = gbBoolean II3
  assert( G == correctSolution )
///


TEST ///
  R = ZZ/2[ vars(1..20)]
  QR = R / ideal apply(gens R, x -> x^2 + x)
  II5 = ideal(l,c*g*h*k*q+c*h*k*q+c*k*q+h*k*q+g*k+h*q+k+1,b*f*k*q*t+b*f*k*t+b*t+q,c*d*j*k+c*d*j*t+c*d*k*t+d*j*k+j*k*t+d*j+j*k+j,e*j*p*q*u+e*j*q*u+e*j+e*q+p*q+q,c*k*m*s*u+c*k*m*u+c*k*m+k*m*s+k*m*u+k*u+m*u+m,b*f*g*r+e*f*g*r+e*f*r+f*g+e*r,f*k*l*u+i*k*l*u+f*l*u+k*l*u+i*k+i*l+k*l+k,f*l*o+f*n+l*o+n*o+l*u,d*e*g*n+d*n+g,d*j*m*o+d*e*o+d*o+m*o+1,f*g*h*i+f*g*h+f*g*i+f*g*q+h*i+1,d*p*r*s+d*p*s+f*r+f*s+f,b*j*k*q*r+b*j*k*q+j*k*q*r+b*q,d*f*g*n+d*f*p+f*n*p+g*n*p+d*g+g*p+1,k*p*q,h*l*o+h*n*r+h*o*r+l*o*r+n*o*r+l+o,f*p*u+c*f+p*u+1,d*h+d,b*g*h+h)
  assert( gbBoolean II5 == ideal matrix {{1_QR}})
///

TEST ///
  R = ZZ/2[ vars(1..20), MonomialOrder=>Lex]
  QR = R / ideal apply(gens R, x -> x^2 + x)
  II6 = ideal(b*c*e*j+b*c*j*n+b*e*j*n+c*e+c*n+c,g*k+g,d*e*f*o+d*f*o*r+d*f*o+e*f*o+d*e*r+e+1,f*s+n*s,d*e*j*o+d*e*j*q+d*j*o*q+e*j*o+d*j*q+e*o+d+o,f*i*n+f*n,f*j*l*p+f*j+j*l,e*k*n*s+e*g*s+e*n*s+g*s+g,c*p*s*t+c*j*t+s,c*k+f,b*e*f+b*e*o+b*o*t+e*o*t+b*o+f*o,b*g+f*q+q,i*m+b*t+k,e*i*l+e*i*m+h*i+h*m+e+1,r*t+1,d*m,d*f*p+e*p*q+f*p*q+d*f+d*p,e*i*m+e*i*p+i*m*p+e*m+f*p+f+i+p,e*g*h*i*u+g*h*i*u+g*h+h*i,c*q+i*q)
  GG = gbBoolean II6
  correctSolution = ideal gens gb (II6, Algorithm=>Sugarless)
  assert(GG == correctSolution )
///

TEST ///
  R = ZZ/2[ vars(1..20)]
  QR = R / ideal apply(gens R, x -> x^2 + x)
  II4 = ideal (d*h*j + h*j*o + d*k*o + j*k*o + d*k + d + h, e*f*o*q + e*g*o + f*g*o + e*g + f*q + g*q + g + 1, h*l*n + j*n*r, q*u + f + q + 1, b*j + h*n, l*m*o + l*q, f*h*o*q + f*h*o + f*o*t + h*q*t + h + 1, g*h*p*r + g*h*r + g*p*r + h*p*r + g*r + h*r + p*r + h + m, d*k + d*r + f*r + k, b*j*o*p*s + b*j*p*s + b*j*p + b*o + b + p + 1, g*r, e*j*r*s + o*r*s + o*r + r*s + e + j + s, m*u + n*u, i*j*p*q + h*i + h*p + j + q, e*l*t*u + d*e*l + e*l*t + d*l*u + e*l*u + d, e*l*m*r + e*l*m*s + l*m*r + l*r*s + m*r*s + l*m, j*m*q*r*t + j*m*q + j*m*t, b*d*r*u + d*p*r*u + d*p*u + b*p + d*p + b*r + p, c*e*m*s, d*e*q*u + e*u + q*u + q)
  GG = gbBoolean II4
  assert( GG == ideal matrix {{1_QR}})
///
----

end

restart

loadPackage "BooleanGB"
loadPackage "BenchmarkGb"
installPackage "BenchmarkGb"
check "BenchmarkGb"
viewHelp runBenchmark

R = ZZ/2[x,y,z]
I = ideal(x+y)
runBenchmark (I, "outputtmp.txt")
"outputtmp.txt" << close

I = II6
 R = ambient ring I;
 p := char R;
 assert( p == 2 );
 FP := ideal apply( gens R, x -> x^2 + x);
 Rlex = ZZ/(char R)[gens R, MonomialOrder=>Lex];
 QRlex = Rlex/ sub( FP, Rlex);
 T = timing gens gb( sub( I, QRlex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
