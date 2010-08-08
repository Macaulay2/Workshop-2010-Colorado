-------Generate all the partitions of a set
-------of a given shape
locS = local locS;
locL = local locL;
locLengthL = local locLengthL;
locParts = local locParts;
locPartitions = local locPartitions;
genPartitions = local genPartitions;

genPartitions = method()
genPartitions(ZZ) := (k)->
(
     if k==length locS then (locPartitions = locPartitions | {set toList locParts}) else
     (
     for i from 0 to locLengthL-1 do
     	  if (i==0 and #locParts#0 < locL#0) or (((locL#(i-1)>locL#i) or (#locParts#(i-1)>0)) and (#locParts#i<locL#i)) then
	  (
	       locParts#i = locParts#i + set{locS#k};
	       genPartitions(k+1);
	       locParts#i = locParts#i - set{locS#k};
	       );
     )
);

Partitions = method()
Partitions(Set,List) := (S,L)->
(
     locS = toList S;
     locL = L;
     locLengthL = #L;
     locParts = new MutableList;
     for i from 0 to locLengthL-1 do locParts#i = set{};
     locPartitions = {};
     genPartitions(0);
     locPartitions
     )
Partitions(Set,Partition) := (S,L)-> Partitions(S,toList L)
--------end generate partitions

-----------------------------
-----Symmetric functions-----
-----------------------------

maxParts = 12
--symFunctions = local symFunctions

----Precalculate correspondence between symmetric functions
EH = local EH
HE = local HE
PH = local PH
HP = local HP
EP = local EP
PE = local PE
--grbH = local grbH
--grbE = local grbE
--grbP = local grbP
grbH = global grbH
grbE = global grbE
grbP = global grbP

makeCorrForH = nParts ->
(
     use symFunctions;
     EH = new MutableList from splice{nParts+1:0};
     PH = new MutableList from splice{nParts+1:0};
     EH#0 = 1_symFunctions;
     for n from 1 to nParts do
     (
	  EH#n = (-1)^(n-1) * sum for j from 0 to n-1 list (-1)^j * EH#j * h_(n-j);
 	  PH#n = n*h_n - sum for j from 1 to n-1 list h_j * PH#(n-j);
	  );
     grbH = forceGB matrix{flatten apply(splice{1..nParts},i->{p_i-PH#i,e_i-EH#i})};
     )

makeCorrForE = nParts ->
(
     use symRingForE;
     HE = new MutableList from splice{nParts+1:0};
     PE = new MutableList from splice{nParts+1:0};
     HE#0 = 1_symRingForE;
     for n from 1 to nParts do
     (
 	  HE#n = - sum for j from 1 to n list (-1)^j * e_j * HE#(n-j);
 	  PE#n = (-1)^(n-1)*n*e_n - sum for j from 1 to n-1 list (-1)^j * e_j * PE#(n-j);
	  );
     grbE = forceGB matrix{flatten apply(splice{1..nParts},i->{p_i-PE#i,h_i-HE#i})};
     )

makeCorrForP = nParts ->
(
     use symRingForP;
     EP = new MutableList from splice{nParts+1:0};
     HP = new MutableList from splice{nParts+1:0};
     EP#0 = HP#0 = 1_symRingForP;
     for n from 1 to nParts do
     (
	  EP#n = -1/n * sum for j from 1 to n list (-1)^j * p_j * EP#(n-j);
	  HP#n = 1/n * sum for j from 1 to n list p_j * HP#(n-j);
	  );
     grbP = forceGB matrix{flatten apply(splice{1..nParts},i->{e_i-EP#i,h_i-HP#i})};
     )
-------end precalculate correspondence

----Precalculate ideals (Groebner bases) of relations among h,e,p
{*makeGrbH = nParts ->
(
     use symFunctions;
     HE = new MutableList from splice{nParts+1:0};
     HP = new MutableList from splice{nParts+1:0};
--     IdealH = {};
     for n from 1 to nParts do
     (
--     	  IdealH = IdealH | {h_n + (-1)^n*e_n + sum for j from 1 to n-1 list (-1)^j * e_j * h_(n-j)};
--	  IdealH = IdealH | {n*h_n - p_n - sum for j from 1 to n-1 list h_j * p_(n-j)};
	  h_0 = 1_symFunctions;
     	  e_0 = 1_symFunctions;
 	  HE#n = - sum for j from 1 to n list (-1)^j * e_j * h_(n-j);
	  HP#n = 1/n * sum for j from 1 to n list p_j * h_(n-j);
	  );
--     grbH = forceGB matrix{IdealH};
     )

makeGrbE = nParts ->
(
--     use symRingForE;
     EH = new MutableList from splice{nParts+1:0};
     EP = new MutableList from splice{nParts+1:0};
--     IdealE = {};
     for n from 1 to nParts do
     (
--    	  IdealE = IdealE | {h_n + (-1)^n*e_n + sum for j from 1 to n-1 list (-1)^j * e_j * h_(n-j)};
--	  IdealE = IdealE | {p_n + (-1)^n*n*e_n + sum for j from 1 to n-1 list (-1)^j * e_j * p_(n-j)};
	  h_0 = 1_symFunctions;
     	  e_0 = 1_symFunctions;
	  EH#n = (-1)^(n-1) * sum for j from 0 to n-1 list (-1)^j * e_j * h_(n-j);
	  EP#n = -1/n * sum for j from 1 to n list (-1)^j * p_j * e_(n-j);
	  );
--     grbE = forceGB matrix{IdealE};
     )

makeGrbP = nParts ->
(
--     use symRingForP;
     PH = new MutableList from splice{nParts+1:0};
     PE = new MutableList from splice{nParts+1:0};
--     IdealP = {};
     for n from 1 to nParts do
     (
--	  IdealP = IdealP | {n*h_n - p_n - sum for j from 1 to n-1 list h_j * p_(n-j)};
--	  IdealP = IdealP | {p_n + (-1)^n*n*e_n + sum for j from 1 to n-1 list (-1)^j * e_j * p_(n-j)};
 	  PE#n = (-1)^(n-1)*n*e_n - sum for j from 1 to n-1 list (-1)^j * e_j * p_(n-j);
 	  PH#n = n*h_n - sum for j from 1 to n-1 list h_j * p_(n-j);
	  );
--     grbP = forceGB matrix{IdealP};
     )
*}

--get Groebner basis for s-functions
--needs initSymRing(maxParts,IncludeS=>true)
IdealS = local IdealS
grbS = local grbS
parti = local parti
pie = local pie

makeGrbS = nParts ->
(
     IdealS = {};
     for i from 1 to nParts do
        for j from 1 to nParts-i do
     	(
	  parti = partitions i;
	  for k from 0 to #parti-1 do
	  (
	       pie = pieri(parti#k,j);
	       IdealS = IdealS | {s_(parti#k)*s_(new Partition from {j})-sum apply(pie,u->s_(new Partition from u))};
	       )
	  );
     grbS = gb(ideal IdealS,DegreeLimit => nParts);
)
--end get grb

----end precalculate ideals of relations

varsE = local varsE
varsH = local varsH
varsP = local varsP
varsS = local varsS
degsEHP = local degsEHP
degsS = local degsS

initSymRing = method(Options => {IncludeS => false,PreCalculateRelations => true})
initSymRing(ZZ) := opts -> (nParts)->
(
     maxParts = nParts;
     varsE = toList(e_1..e_(nParts));
     varsP = toList(p_1..p_(nParts));
     varsH = toList(h_1..h_(nParts));
     degsEHP = toList(1..nParts);
     varsS = degsS = {};

     if opts.IncludeS then
     (
	  for i from 1 to nParts do
     	  (
	       pars := partitions i;
     	       for j from 0 to #pars-1 do
	       varsS = varsS | {s_(pars#j)};
	       degsS = degsS | toList(#pars:i);
	       );
	  );

     variables := varsE | varsP | varsH | varsS;
     degs := degsEHP | degsEHP | degsEHP | degsS;
     symFunctions = QQ[variables,Degrees=>degs,MonomialOrder=>GRevLex];

     blocks = {splice{0..maxParts-1},splice{maxParts..(2*maxParts-1)},splice{(2*maxParts)..(3*maxParts-1)}};

     symRingForE = QQ[varsH | varsP | varsE,Degrees=>flatten toList(3:degsEHP),MonomialOrder=>GRevLex];
     mapToE = map(symRingForE,symFunctions,apply(blocks#2|blocks#1|blocks#0,i->symRingForE_i) | toList(#varsS:0));
     mapFromE = map(symFunctions,symRingForE,apply(blocks#2|blocks#1|blocks#0,i->symFunctions_i));

     symRingForP = QQ[varsH | varsE | varsP,Degrees=>flatten toList(3:degsEHP),MonomialOrder=>GRevLex];
     mapToP = map(symRingForP,symFunctions,apply(blocks#1|blocks#2|blocks#0,i->symRingForP_i) | toList(#varsS:0));
     mapFromP = map(symFunctions,symRingForP,apply(blocks#2|blocks#0|blocks#1,i->symFunctions_i));

     if opts.PreCalculateRelations then
     (
	  makeCorrForH nParts;
	  makeCorrForE nParts;
	  makeCorrForP nParts;
     	  );
{*     else
     (
	  makeGrbE nParts;
     	  makeGrbP nParts;
     	  makeGrbH nParts;
	  );
*}
     use symFunctions;
     )

initSymRing(maxParts);

------Pieri rule-------
nr = local nr
lenla = local lenla
aux = local aux
ala = local ala
rez = local rez
pars = local pars

pieri = method()
pieri(Partition,ZZ) := (la,n)->
(
     nr = n;
     lenla = #la;
     aux = reverse toList la;
     ala = aux - ({0} | remove(aux,-1));
     rez = {};
     pars = {};
     backPie(0);
     pars
     )

backPie = method()
backPie(ZZ) := (k)->
(
     if k==lenla then
     (
	  bux = ({0} | aux) + (rez | {nr});
	  if bux#(0)==0 then bux = remove(bux,0);
	  pars = pars | {reverse(bux)};
	  )
     else for i from 0 to min(ala#k,nr) do
     (
	  rez = rez | {i};
	  nr = nr-i;
	  backPie(k+1);
	  nr = nr + i;
	  rez = remove(rez,-1);
	  )
     )
------end Pieri rule

------Write symmetric functions in bases e,h,p,s
symtoe = method()
symtoe(RingElement) := (f)->
(
     mapFromE(mapToE(f)%grbE)
--     aux := f;
--     for i from 1 to maxParts do aux = sub(aux,{h_i => HE#i, p_i => PE#i});
--     for j from 1 to maxParts do (i = maxParts+1-j;aux = sub(aux,{h_i => HE#i, p_i => PE#i}););
--     aux
     )

symtoh = method()
symtoh(RingElement) := (f)->
(
     f%grbH
--     aux := f;
--     for j from 1 to maxParts do (i = maxParts+1-j;aux = sub(aux,{e_i => EH#i, p_i => PH#i}););
--     aux
     )

symtop = method()
symtop(RingElement) := (f)->
(
     mapFromP(mapToP(f)%grbP)
--     aux := f;
--     for j from 1 to maxParts do (i = maxParts+1-j;aux = sub(aux,{e_i => EP#i, h_i => HP#i}););
--     for i from 1 to maxParts do aux = sub(aux,{h_i => HP#i, e_i => EP#i});
--     aux
     )

symtos = method()
symtos(RingElement) := (f)->
(
     hf := symtoh(f);
--     A := schurRing(s,maxParts);
--     symToA := map(A,symFunctions,gens A | splice{maxParts:0} | apply(splice{1..maxParts},i->s_{i}));
--     symToA(hf)
     rez := {};
     while (hf!=0) do
     (
     	  lt := leadTerm hf;
     	  (mon,coe) := coefficients lt;
     	  degs := (flatten exponents mon_0_0)_{(2*maxParts)..(3*maxParts-1)};
     	  par := {};
     	  for i from 0 to maxParts-1 do
	      par = par | splice{degs#i:(i+1)};
	  par = reverse par;
	  hf = hf - coe_0_0*(jT(par));--symtoh
	  rez = rez | {(coe_0_0,par)};
--	  print(#rez);
     );
     rez
     )
------end symmetric functions in bases e,h,p,s

------Jacobi-Trudi determinantal identity
------improvement: if lambda' has fewer rows use e's
jacTrudi = method()
jacTrudi(Partition) := (lambda) -> 
(
     lam := lambda;
     u := h;
{*     lam' := conjugate lam;
     if #lam'<#lam then
     (
	  u = e;
	  lam = lam';
	  );*}
     n := #lam;
     det map(symFunctions^n, n, (i,j) -> 
	  (
	       aux := lam#i-i+j;
	       if aux < 0 then 0_symFunctions
	       else if aux == 0 then 1_symFunctions else u_aux)
	       )
     )
jacTrudi(List) := (lambda) -> jacTrudi(new Partition from lambda)

S = new MutableHashTable

jT = method()
jT(List) := (lambda) ->
(
     rez := local rez;
--     if S#?lambda then rez = S#lambda
--     else
--     (
     ll := #lambda;
     if ll == 0 then rez = 1_symFunctions else
     if ll == 1 then rez = h_(lambda#0) else
     (
	  l1 := drop(lambda,-1);
     	  l2 := {};
	  rez = 0;
	  sgn := 1;
	  for i from 0 to ll-1 do
	  (
     	       rez = rez + sgn*h_(lambda#(ll-1-i)+i)*jT(l1|l2);
	       sgn = - sgn;
	       l1 = drop(l1,-1);
	       if lambda#(ll-1-i)>1 then
	       l2 = {lambda#(ll-1-i)-1} | l2;
	       );
	  );
--     S#lambda = rez;
--     );
     rez
     )
------end Jacobi-Trudi

-----Littlewood-Richardson------
LR = method()
LR(List,List) := (lambda,mu) ->
(
     symtos(jacTrudi(lambda)*jacTrudi(mu))
     )
-----end Littlewood-Richardson


------Plethysm
plet = local plet
plethysm = method()
plethysm(RingElement,RingElement) := (f,g)->
(
     pf := symtop(f);
     pg := symtop(g);
     su := {p_1 => pg};
     for i from 2 to maxParts do
     if pf//p_i != 0 then
     (
	  aux := splice{1..(maxParts//i)};
	  su = su | {p_i => sub(pg,apply(aux,j->(p_j => p_(i*j))))};
	  );
     plet = sub(pf,su);
     plet
--     symtos(plet)
)
--use the code below if one has a Groebner basis for S-functions
--splet = sub(hplet,apply(splice{1..maxParts},i->(h_i => s_(new Partition from {i}))))
--splet%grbS
------end plethysm

----new symmetric functions
symPlet = method()
symPlet(List) := lambda ->
(
     lam := toList(conjugate(new Partition from lambda)) | {0};
     pol := 1_symFunctions;
     for i from 0 to #lam-2 do
     (
	  del := lam#i - lam#(i+1);
	  if del>0 then pol = pol * plethysm(h_del,h_(i+1));
	  );
     pol
     )
symPlet(Partition) := lambda -> symPlet(toList lambda)

partns = method()
partns(ZZ,ZZ) := (d, n) -> (
     -- d is an integer >= 0
     -- n is an integer >= 1
     -- returns a list of all of the partitions of d
     --    having <= n parts.
     x := partitions(d);
     select(x, xi -> #xi <= n))     

toSchur = method()
toSchur(List) := ple ->
(
pol := 0_A;
for i from 0 to #ple-1 do
     pol = pol + lift(ple#i#0,QQ)*s_(ple#i#1);
pol     
)
end

----
restart
time load "symm.m2"
time initSymRing(30,PreCalculateRelations => true)
time symtos(plethysm(h_5,h_6));

gbTrace=3
gens grbH;