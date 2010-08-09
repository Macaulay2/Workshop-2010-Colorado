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
export {runBenchmark}

-- Code here

runBenchmark = method()
runBenchmark Ideal := Ideal => I -> (
 R = ambient ring I;
 p := char R;
 assert( p == 2 );
 FP := ideal apply( gens R, x -> x^2 + x);

 Rlex = ZZ/(char R)[gens R, MonomialOrder=>Lex];
 T := timing gens gb( sub( I, Rlex) + sub( FP, Rlex) );
 tt := first T;
 G := last T;
 print ("Lex Order of (I+FP): " | toString tt | " seconds.");

 RgRevLex = ZZ/(char R)[gens R, MonomialOrder=>GRevLex];
 T = timing gens gb( sub( I, RgRevLex) + sub( FP, RgRevLex) );
 tt = first T;
 G = ideal last T;
 print ("GRevLex Order of (I+FP): " | toString tt | " seconds.");

 T = timing gens gb( sub( G, Rlex) + sub( FP, Rlex) );
 tt = first T;
 G = ideal last T;
 print ("Lex order from GRevLex basis of (I+FP): " | toString tt | " seconds.\n");

 QRlex = Rlex/ sub( FP, Rlex);
 T = timing gens gb( sub( I, QRlex));
 tt = first T;
 G = last T;
 print ("Quotient Ring Lex Order: " | toString tt | " seconds.");

 QRgRevLex = RgRevLex/ sub( FP, RgRevLex);
 T = timing gens gb( sub( I, QRgRevLex));
 tt = first T;
 G = last T;
 print ("Quotient Ring GRevLex Order: " | toString tt | " seconds.");

 T = timing gens gb( sub( G, QRlex));
 tt = first T;
 G = last T;
 print ("Quotient Ring GRevLex Order: " | toString tt | " seconds.\n");
 
 T = timing gens gb( sub( I, QRlex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
 print ("Quotient Ring Lex Order, Sugarless: " | toString tt | " seconds.");

 T = timing gens gb( sub( I, QRgRevLex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
 print ("Quotient Ring GRevLex Order, Sugarless: " | toString tt | " seconds.");

 T = timing gens gb( sub( G, QRlex), Algorithm=>Sugarless);
 tt = first T;
 G = last T;
 print ("Quotient Ring GRevLex Order, Sugarless: " | toString tt | " seconds.\n");
 
 T = timing gbBoolean I;
 tt = first T;
 G = last T;
 print ("gbBoolean: " | toString tt | " seconds.");
 
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

TEST ///
  R = ZZ/2[x,y,z]
  I = ideal(x+y,x)
  runBenchmark I 
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
runBenchmark I 

