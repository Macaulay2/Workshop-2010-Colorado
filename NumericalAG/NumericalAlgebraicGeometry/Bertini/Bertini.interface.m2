-- Bertini interface for NAG4M2
-- used by ../NumericalAlgebraicGeometry.m2

solveBertini = method(TypicalValue => List)
solveBertini (List,HashTable) := List => (F,o) -> (
	  -- tempdir := temporaryFileName() | "NumericalAlgebraicGeometry-bertini";
	  -- mkdir tempdir; 	  
  	  makeBertiniInput F;
  	  run(BERTINIexe|" >bertini_session.log");
	  sols := readSolutionsBertini("finite_solutions");
	  result = sols;
	  -- remove Bertini input/output files
    	  for f in {"failed_paths", "nonsingular_solutions",
               "raw_data", "start", "input", "output", "raw_solutions",
               "main_data", "real_finite_solutions", "finite_solutions",
               "midpath_data", "singular_solutions", "real_solutions",
               "singular_solutions", "midpath_data"} do
          if fileExists f then removeFile f;
	  result
	  )

makeBertiniInput = method(TypicalValue=>Nothing, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii})
makeBertiniInput List := o -> T -> (
-- IN:
--	T = polynomials of target system
--      o.StartSystem = start system
  v := gens ring T#0; -- variables
  f := openOut "input"; -- THE name for Bertini's input file 
  f << "CONFIG" << endl;
  --f << "MPTYPE: 2;" << endl; -- multiprecision
  f << "MPTYPE: 0;" << endl; -- double precision (default?)
  if #o.StartSystem > 0 then
    f << "USERHOMOTOPY: 1;" << endl;
  f << endl << "END;" << endl << endl;
  f << "INPUT" << endl << endl;
  if #o.StartSystem > 0 then
    f << "variable "
  else f << "variable_group "; -- variable section
  scan(#v, i->
       if i<#v-1 
       then f << toString v#i << ", "
       else f << toString v#i << ";" << endl
       );
  f << "function "; -- "function" section
  scan(#T, i->
       if i<#T-1
       then f << "f" << i << ", "
       else f << "f" << i << ";" << endl << endl
      );
  bertiniNumbers := p->( L := toString p; 
       L = replace("ii", "I", L); 
       L = replace("e", "E", L);
       L
       );
  if #o.StartSystem == 0 
  then scan(#T, i -> f << "f" << i << " = " << bertiniNumbers T#i << ";" << endl)
  else (
       if #o.StartSystem != #T then error "expected equal number of equations in start and target systems";
       f << "pathvariable t;" << endl 
         << "parameter s;" << endl
         << "s = t;" << endl;
       scan(#T, i -> f << "f" << i 
	    << " = (" << bertiniNumbers T#i << ")*(1-s)+s*("<< bertiniNumbers o.gamma << ")*(" << bertiniNumbers o.StartSystem#i << ");" << endl 
	   );
       );
  f << endl << "END" << endl << endl;
  close f;
  
  if #o.StartSolutions > 0 then (
       f = openOut "start"; -- THE name for Bertini's start solutions file 
       f << #o.StartSolutions << endl << endl;
       scan(o.StartSolutions, s->(
		 scan(s, c-> f << realPart c << " " << imaginaryPart c << ";" << endl );
		 f << endl;
		 ));
       close f;
       );
  )

cleanupOutput = method(TypicalValue=>String)
cleanupOutput String := s -> (
-- cleanup output (Bertini and hom4ps2)
  t := replace("E", "e", s);
  t = replace("[(,)]","", t);
  t = replace("e\\+","e",t)
  )

readSolutionsBertini = method(TypicalValue=>List)
readSolutionsBertini String := f -> (
  s := {};
  if f == "finite_solutions" then (
       print "implementation unstable: Bertini output format uncertain";
       l := lines get f;
       nsols := value first separate(" ", l#0);
       l = drop(l,2);
       while #s < nsols do (	 
	    coords := {};
	    while #(first l) > 2 do ( 
	      	 coords = coords | {(
		   	   a := separate(" ",  cleanupOutput(first l));	 
		   	   (value a#0)+ii*(value a#1)
	      	   	   )};
    	      	 l = drop(l,1);
	      	 );	
	    l = drop(l,1);
            if DBG>=10 then << coords << endl;
	    s = s | {{coords}};
	    );	
       ) 
  else if f == "raw_solutions" then (
       l = lines get f;
       while #l>0 and #separate(" ", l#0) < 2 do l = drop(l,1);
       while #l>0 do (
	    if DBG>=10 then << "------------------------------" << endl;
	    coords = {};
	    while #l>0 and #separate(" ", l#0) >= 2 do ( 
	      	 coords = coords | {(
		   	   a = separate(" ",  cleanupOutput(first l));	 
		   	   (value a#0)+ii*(value a#1)
	      	   	   )};
    	      	 l = drop(l,1);
	      	 );
	    while #l>0 and #separate(" ", l#0) < 2 do l = drop(l,1);
            if DBG>=10 then << coords << endl;
	    s = s | {{coords}};
	    );     
    ) else error "unknow output file";
  s
  )

trackBertini = method(TypicalValue => List)
trackBertini (List,List,List,HashTable) := List => (S,T,solsS,o) -> (
     -- tempdir := temporaryFileName() | "NumericalAlgebraicGeometry-bertini";
     -- mkdir tempdir; 	  
     makeBertiniInput(T, StartSystem=>S, StartSolutions=>solsS, gamma=>o.gamma);
     compStartTime = currentTime();      
     run(BERTINIexe|" >bertini_session.log");
     if DBG>0 then << "Bertini's computation time: " << currentTime()-compStartTime << endl;
     result := readSolutionsBertini("raw_solutions");
     -- remove Bertini input/output files
     if DBG<10 then (
	  for f in {"failed_paths", "nonsingular_solutions",
	       "raw_data", "start", "input", "output", "raw_solutions",
	       "main_data", "real_finite_solutions", "finite_solutions",
	       "midpath_data", "singular_solutions", "real_solutions",
	       "singular_solutions", "midpath_data"} do
     	  if fileExists f then removeFile f;
	  );
     result
     )
     
