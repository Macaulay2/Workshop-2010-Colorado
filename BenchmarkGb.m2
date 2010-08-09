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

 Rlex := ZZ/(char R)[gens R, MonomialOrder=>Lex];
 T := timing gens gb( sub( I, Rlex));
 tt := first T;
 G := last T;
 print ("Lex Order: " | toString tt | " seconds.");

 RgRevLex := ZZ/(char R)[gens R, MonomialOrder=>GRevLex];
 T = timing gens gb( sub( I, RgRevLex));
 tt = first T;
 G = last T;

 print ("GRevLex Order: " | toString tt | " seconds.");
 T = timing gens gb( sub( G, Rlex));
 tt = first T;
 G = last T;
 print ("Lex order from GRevLex basis: " | toString tt | " seconds.")
)

end

loadPackage "BenchmarkGb"
R = ZZ/2[x,y,z]
I = ideal(x+y)
runBenchmark I 

  


 n := numgens R;

  -- work in R, first Lex, then gRevLev -> Lex
  
 timing G = 
 QR = makeRing(n,p); -- quotient ring
)





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
