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
