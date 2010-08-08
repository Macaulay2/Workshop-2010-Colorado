newPackage("SEM",
     Authors => {
	  {Name => "Luis Garcia"},
	  {Name => "Alexander Diaz"}
	  },
     DebuggingMode => false,
     Headline => "Gaussian Library Translation",
     Version => "1"
     )

--loadPackage "Gausianlib"

--this is a comment
--the main data type will be a graph
--it will consist of two hash tables
--the first hash table will have each node => list of its children
--the second hash will be for bidirected edges and will have each node => list of its children
--example of a list: x = {1, 2, 3, 4}
--example of a hash table: g1 = new HashTable from {1 => {2}, 2 => {3,4}, 3 => {}, 4 => {}}

--example of the data structure "graph":
--g1 = new HashTable from {1 => {2}, 2 => {3,4}, 3 => {}, 4 => {}}
--g2 = new HashTable from {1 => {2}, 2 => {1}, 3 => {}, 4 => {}}
--graph = {g1, g2}


export {msize, shift, nonzerosize, Sring, Pring, Lring, binary}


msize = method()
msize(ZZ) := (n) -> (n*(n-1)/2);

shift = method()
shift(List) := (v) -> (
	myv := new MutableList from v;
	for i from 0 to (#v-1) do (myv#i = myv#i -1);
	toList(myv))

nonzerosize = method()
nonzerosize(List) := (v) -> (
	num:=0;
	for i from 0 to (#v-1) do (
		if(v#i != 0) then
		(num = num + 1));
	num)

Sring = method()
Sring(ZZ) := (n) -> (
	slist := {};
	for i from 1 to n do (
		for j from 1 to n do (
			slist = slist|{getSymbol((toString(s)|toString(i)|toString(j)))}
		)
	);
	QQ[slist])

Pring = method()
Pring(ZZ, List) := (n, g) -> (
	plist := {};
	for i from 1 to n do (
		for j from 1 to n do (
			if(i == j) then (
				plist = plist|{getSymbol((toString(p)|toString(i)|toString(j)))}
			);
			if(i < j) then (
				for k from 0 to (#g#1#i-1) do (
					if(g#1#i#k == j) then (
						plist = plist|{getSymbol((toString(p)|toString(i)|toString(j)))}
					);
				);
			);
		);
	);
	QQ[plist])
	
Lring = method()
Lring(ZZ, List) := (n, g) -> (
	llist := {};
	for i from 1 to n do (
		for j from 1 to n do (
			if(i == j) then (
				llist = llist|{getSymbol((toString(l)|toString(i)|toString(j)))}
			);
			if(i < j) then (
				for k from 0 to (#g#1#i-1) do (
					if(g#1#i#k == j) then (
						llist = llist|{getSymbol((toString(l)|toString(i)|toString(j)))}
					);
				);
			);
		);
	);
	QQ[llist])

identify = method()
identify(List, List) := (u, v) -> (
	n := #u#0;
	S := Sring(n);
	P := Pring(v);
	L := Lring(u);
	Q := QQ[q];
	QS := Q**S;
	LP := L**P;
	SL := S**L;
	QSLP := QS**LP;
	
	MP := map(S^n,n,(i,j)->S_(((n-1)*i)+(i+j)));
	PM := map(P^n,n,(i,j)->0);
	LM := map(L^n,n,(i,j)->0);
	
	use LP;
	Linv = LM^-1;
	LiPL = transpose(Linv)*PM*Linv;
	temp = flatten LiPL;
	

)

--edge color method

--trek separation method

--separate method

--there is an isSubset method
--a = {1,2,3,4}
--isSubset({1,2}, set a)
--true

--there is a subtraction of sets method
--a = {1,2,3,4} b = {3,4}
--set a - set b
--{1,2}

--there is an intersection of sets
--a = {1,2,3,4} b = {1,3,5}
--set a * set b
--{1,3}

--add_statement method

trek_ideal = method();
trek_ideal(ZZ, List) := (n, constraints) -> (
	M = map(ZZ^n,n,(i,j)->0);
	M = mutableMatrix M;
	k = 1;
	for i from 1 to n do (
		for j from 1 to n do (
			M_(i,j) = k;
			M_(j,i) = k;
			k = k+1;
		);
	);
	
	for i from 1 to #constraints do (
		A = constraints_i_1;
		B = constraints_i_2;
		C = {};
		if (constraints_i_3 != 0) then (
			C = join (C,constraints_i_3);
		);
		if (constraints_i_4 != 0) then (
			C = join (C,constraints_i_4);
		);
		if (C != 0) then (
			D = set C - set A;
			if (D!=0) then (
				A = join (A,D);
			);
			D = set C - set B;
			if (D!=0) then (
				B = join (B,D);
			);
			s = #C + 1;
		);
		else (
			s = 1;
		);
		m = submatrix'(M, A, B);
		I = I + minors(m,s);
	);
	G = groebnerBasis I;
	ideal G
)

is_determinantal = method()
is_determinantal(Ideal, Ideal) := (K, I) -> (
	returnlist = {};
	flag = 1;
	out = {};
	for i from 1 to (numgens K) do (
		if (K_i # I !=) then (
			out = append (out, i);
			if (flag == 1) then (
				flag = 0;
			);
		);
	);
	append (returnlist, flag);
	append (returnlist, out);
	returnlist
)

binary = method()
binary(ZZ,ZZ) := (n, N) -> (
	d := n/2;
	b = new MutableHashTable
	scan(0..N, i -> b#i = i)
	k := N
	b#k = n%2;
	for k from N-1 to 0 do (
		b#k = d%2;
		d = d/2;
	);
	values b;
)

--kickit

--kickit_iso

--single_door

--instrumental variable

--back_door

