ISSUE 1:
--sub has nasty, unexpected coercion behavior that is likely to cause bugs for many users;
--one example:
--it turns out that substituting integers into a polynomial with rational coefficients will
--somehow coerce the polynomial into a polynomial ring over ZZ before substituting

--A simple example of this ugly decision:
restart
S = QQ[x]
p = (1/2)*x
sub(p,{x=>2}) --returns 2, not 1

ISSUE 2:
--It would be great if there were highlighting (in emacs) for methods and Types supplied by
--loaded packages.  Would make coding much easier.