Okay, I've copied all these ideas into

    svn://svn.macaulay2.com/Macaulay2/trunk/M2/Macaulay2/bugs/dan/1-FromMethod

Since complicated new syntax has been suggested (List from x, Matrix of ZZ from {{3}})
this is going to take some time.

Thanks to everyone!

Dan

=============================================================================

-- Everyone is invited to enter their proposed code for doing conversions from
-- one type to another, use "new ... from ..." methods.  Find your name below
-- and add it there, to avoid conflicts.

-- Try your test first, to see if your proposed functionality doesn't yet exist, like this:

	-- i20 : R = QQ[x..z];

	-- i21 : new List from vars R
	-- stdio:21:1:(3): error: expected a list (in absence of a 'new' method)


-- Here are the previously existing (non-built-in) methods:

    -- i1 : methods NewFromMethod 

    -- o1 = {(NewFromMethod, Command, Function)           }
    --      {(NewFromMethod, Command, String)             }
    --      {(NewFromMethod, DocumentTag, List)           }
    --      {(NewFromMethod, Eliminate, ZZ)               }
    --      {(NewFromMethod, EngineRing, RawRing)         }
    --      {(NewFromMethod, HashTable, List)             }
    --      {(NewFromMethod, IndexedVariableTable, Symbol)}
    --      {(NewFromMethod, Manipulator, Function)       }
    --      {(NewFromMethod, Matrix, MutableMatrix)       }
    --      {(NewFromMethod, Matrix, Vector)              }
    --      {(NewFromMethod, Module, List)                }
    --      {(NewFromMethod, Module, Sequence)            }
    --      {(NewFromMethod, MonoidElement, RawMonomial)  }
    --      {(NewFromMethod, MutableMatrix, Matrix)       }
    --      {(NewFromMethod, Set, List)                   }
    --      {(NewFromMethod, URL, String)                 }
    --      {(NewFromMethod, Vector, Matrix)              }

    -- o1 : VerticalList

-- Feel free to install others that don't conflict with these.
-- Give examples of use.

new List from Matrix := (List,m) -> entries m				    -- proposed by Charley Crissman
{*
R = QQ[x..z];
new List from vars R
*}

new List from Set := (List,x) -> elements x				    -- proposed by Charley Crissman
{*
new List from set {a,b,c}
*}

new List from Tally := (List, x) -> splice apply(pairs x,(k,v) -> v:k)
{*
tally {1,1,2,a,a,a,b,c,c,d}
new List from oo
assert( tally oo === ooo )
*}

new Matrix from List := (Matrix,v) -> matrix v
-- This one will not work currently, because:
--     (1) Matrix is a type of HashTable
--     (2) there is already a (built-in) method for new HashTable from List
--     (3) the internal code uses the method for new HashTable from List
-- I'll fix that in the engine eventually.


new String from Number := (String,x) -> toString x
{*
new String from 1234.56
ascii oo
*}

new RingElement from Number := (R,x) -> try promote(x,R) else error("conversion to type ",toString R," not possible")
{*
R = QQ[x]
new R from 3
*}

new Number from Number := 
new RingElement from RingElement := (R,x) -> try promote(x,R) else try lift(x,R) else error("conversion to type ",toString R," not possible")
{*
R = QQ[x]
S = R[y]
x
new S from x
new R from oo
new S from 3 --charleyc says: requires new RingElement from Number conversion above
new R from oo
new QQ from 3
new ZZ from oo
new ZZ from 3/2
*}

new Number from RingElement := (R,x) -> try lift(x,R) else error("conversion to type ",toString R," not possible")
{*
R = QQ[x]
new R from 1/2
new QQ from oo
new ZZ from ooo
*}

-- Hirotachi Abo

-- Beth Arnold

-- Brett Barwick

-- Charley Crissman
-- Extend syntax to allow expressions like:
-- new Matrix of S from X
-- which will make a matrix of elements of S from X by applying the coercion "new S from e"
-- for each entry e of X (while also dealing correctly with gradings)
--
--code:
-- new Matrix of RingElement from Matrix := (Matrix, R, m) -> (
--     try promote(m,R) else try lift(m,R) else error("conversion to type ",toString R," not possible.")
--
-- Example of where this would be nice:
-- R = ZZ/32003
-- M = matrix(R,{{1,2},{3,4}})
-- new Matrix of ZZ from X
--
-- This syntax would also give a suitable replacement for the current nasty coercion behaviour of
-- sub over QQ, which causes sub((1/2)*x, {x=>2}) to return 2, not 1

new Matrix from Number :=
new Matrix from RingElement := (Matrix, x) -> matrix {{x}}
{*
new Matrix from 3
R = QQ[x]
new Matrix from x+1
*}

new List from BasicList := (List, L) -> toList L
{*
L = (1,2,3,4,5)
new List from L
*}

-- Alex Diaz

-- Bill Gary Furnish

-- Luis Garcia-Puente

-- Courtney Gibbons

-- Dan Grayson

-- David Eisenbud

-- Franziska Hinkelmann
new String from List := (String,l) -> toString l
{*
new String from {1,2,1,3,4}
ascii oo
*}



-- Lars Kastner

-- Anton Leykin

-- Shaowei Lin

-- Samuel Lundqvist

-- Abraham Martin del Campo

-- Jason McCullough

-- Dennis Moore

-- Matt Niemerg

-- Sonja Petrovic

-- Claudiu Raicu

-- Eduardo Sáenz-de-Cabezón

-- Jessica Sidman

-- Greg Smith

-- Michael Stillman

-- Branden Stone

-- David Swinarnski

-- Amelia Taylor

-- Doug Torrance

-- Josephine Yu


