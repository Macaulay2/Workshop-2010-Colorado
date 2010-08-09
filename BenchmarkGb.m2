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

 QRgRevLex = RgRevLex/ideal FP;
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
 



)

end

loadPackage "BenchmarkGb"
R = ZZ/2[x,y,z]
I = ideal(x+y)
runBenchmark I 

  
beginDocumentation()

  doc ///
  Key
  BenchmarkGB
  Headline
  Description
  Text
  Example
  Caveat
  SeeAlso
  ///

  doc ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Consequences
  Description
  Text
  Example
  Code
  Pre
  Caveat
  SeeAlso
  ///

  TEST ///
  -- test code and assertions here
  -- may have as many TEST sections as needed
  ///




end
