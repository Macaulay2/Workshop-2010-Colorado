-- Test/Example file for Jason-Ideal.m2
loadPackage "JasonIdeal"
-- Work by Beder, McCullough, Nunez, Seceleanu, Snapp, Stone

-- JJ is the command that creates the ideal.  It accepts as input an integer g >= 2
-- and a tuple {m_1,...,m_n}.  The resulting ideal will have g+1 generators and
-- the m_i's control the entries in the subscript matrices.
-- All generators will have degree m_1 + ... + m_n + 1 by construction.
-- There is one restriction: m_n >=0, m_(n-1) >= 1, all other m_i >= 2.

-- Example 1 - length-one tuple
I = JJ(3,{2})
-- all ideals are guaranteed to be depth 0 (this is a theorem of ours), and thus have
-- full projective dimension
betti res I
pdim (module ring I/I)
dim ring I

-- Example 2 - tuple of the form {1,b}
I = JJ(2,{1,5})
-- These ideals were studied by Caviglia in his thesis.  He showed that 
-- reg JJ(2,{1,b}) = (b + 2)^2 - 1
regularity I
-- These ideals have weakly stable monomial ideals, which allows one to compute the
-- regularity.  I don't think this is true in general.

-- Example 3 - 3-tuples
-- For tuples of the form {2,1,i}, we seem to get cubic growth of regularity
netList for i from 0 to 4 list(
     I := JJ(2,{2,1,i});
     {regularity I,I}
     )

-- Note that these are just 3-generated ideals with generators of degree 4 + i

-- Example 4 - larger tuples
-- It seems that a tuple starting with k "2"s followed by "1,i" has regularity growing
-- asymptotically as (k+2)^i, but these quickly become difficult to compute with.
I = JJ(2,{2,2,1,0},BaseField=>ZZ/32003)
gbTrace = 3
G = time gb(I,Algorithm=>LinearAlgebra)
lt = leadTerm gens G;
betti lt
time regularity ideal lt
dim ring I
regularity I
flatten entries gens G

I = JJ(2,{2,2,2,1,0},BaseField=>ZZ/32003)
gbTrace = 3
time gb(I,Algorithm=>LinearAlgebra)
li = leadTerm gens oo;
--This one times out for me
