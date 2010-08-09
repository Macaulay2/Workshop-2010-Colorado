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


end

restart
load "QStestFile.m2"
R = ZZ/101[x,y,z]
f = matrix{{x^2*y+1,2*x*y,x+y-2}}
w = applyRowShortcut f
f*w
