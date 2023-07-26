---- CSci 119, Spring 2021, Lab 2 ----

import Data.List(sort)

----- PART 1:  Testing properties of relations -----

-- As in Lab 1, we will be working with the finite universe U = [1..8],
-- but your code should work with any universe.
u = [1..8]

-- A relation, R, on U is a list of the ordered pairs of elements of U:
type Reln = [(Int,Int)]
              
-- For example, here are the < and <= relations
less_reln :: Reln
less_reln = [(i,j) | i <- u, j <- u, i < j]

leq_reln :: Reln
leq_reln  = [(i,j) | i <- u, j <- u, i <= j]
            
-- and here is the relation of equivalence mod 3:
eqmod3_reln :: Reln
eqmod3_reln = [(i,j) | i <- u, j <- u, (j - i) `mod` 3 == 0]


-- Write a function refl that tests whether a relation is reflexive:
-- R is reflexive if: forall a, (a,a) in R
-- Example: [(i,i) | i <- u] is the smallest reflexive relation over u.
-- Anything that does not contain all of these 8 elements is not reflexive.
refl :: Reln -> Bool
refl rs = and [elem (i,i)  rs| i<-u]

-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
-- Example: [(1,1), (1,2), (2,1)] is symmetric but [(1,1), (1,2)] is not.
symm :: Reln -> Bool
symm rs = and [elem (j,i) rs | (i,j) <- rs]

-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, ((a,b) in R /\ (b,c) in R) -> (a,c) in R
-- Example: [(1,2),(2,3),(1,3),(4,4)] is transitive but [(2,3),(3,2)] is not
trans :: Reln -> Bool
trans rs = and [elem (a,d) rs|(a, b)<-rs,(c,d)<-rs,b==c]


-- Use the functions above to check the less, leq, and eqmod3 relations for
-- relexivity, symmetry, and transitivity.


----- PART 2:  Finding minimal relations with combinations of properties -----

-- For the following problems, you can assume that u = [1..8].
--
-- For each of the 8 possible combinations of yes/no on reflexivity,
-- symmetry, and transitivity, find a MINIMAL relation on u that has exactly
-- that combination of properties. Add a test to check whether you got the
-- properties right. (I'll do the first one as an example.)

-- refl, symm, trans
rst :: Reln
rst = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8)]
rst_test = refl rst && symm rst && trans rst

-- refl, symm, not trans
rst' :: Reln
rst' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (1,3), (3,5), (3,1), (5,3)]
rst'_test = refl rst' && symm rst' && not(trans rst')

-- refl, not symm, trans
rs't :: Reln
rs't = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8),(1,3),(3,2)]
rs't_test =  refl rs't' && not(symm rs't')  && not(trans rs't')

-- refl, not symm, not trans
rs't' :: Reln
rs't' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8),(1,3),(3,2)]
rs't'_test =  refl rs't' && not(symm rs't')  && not(trans rs't')

-- not refl, symm, trans
r'st :: Reln
r'st = [(5,5)]
r'st_test =  not(refl r'st) && symm r'st && trans r'st

-- not refl, symm, not trans
r'st' :: Reln
r'st' = [(5,1),(1,5)]
r'st'_test =  not(refl r'st') && symm r'st'  && not(trans r'st')

-- not refl, not symm, trans
r's't :: Reln
r's't = [(4,3),(3,7),(4,7)]
r's't_test =  not(refl r's't) && not(symm r's't)  && trans r's't

-- not refl, not symm, not trans
r's't' :: Reln
r's't' = [(1,2),(3,4),(4,7)]
r's't'_test = not(refl r's't') && not(symm r's't') && not(trans r's't')


---- PART 3: Partitions of u -----

-- Again, the functions in this part should work with any finite universe, u

-- A partitition, P, of u is a list of blocks, each of which are lists of
-- elements of u, that satisfies these conditions:
-- nontrivial: forall X in P, exists x in U, x in X;
--             equivalently, [] not in P
-- total:      forall x in U, exists X in P, x in X
-- disjoint:   forall X,Y in P (exists a, a in X /\ a in Y) -> X = Y,
--             equivalently, forall X,Y in P, X /= Y -> X intersect Y = []

--Helper functions for pt 3
empty :: [[Int]] -> Bool
empty cs = or [null (ds) | ds <- cs]

total :: [[Int]] -> Bool
total es = and [ or [x `elem` ds | ds <- es] | x <- u]

disjoint :: [[Int]] -> Bool
disjoint fs = and [ and [ not(x `elem` es)| x <- ds]| ds <- fs, es <- fs, es /= ds]

normalize :: Ord a => [a] -> [a]
normalize xs = remdup (sort xs) where
  remdup [] = []
  remdup [x] = [x]
  remdup(x:y:zs) | x==y = remdup(y:zs)
                 |otherwise = x:remdup(y:zs)

-- For example, here is the partitition of u = [1..8] corresponding to
-- eqmod3_reln:
eqmod3_part :: [[Int]]
eqmod3_part = [[1,4,7], [2,5,8], [3,6]]

-- Write a function, part, that tests whether a list of lists is a partition
-- of u
part :: [[Int]] -> Bool
part bs = not(empty bs) && total bs && disjoint bs


-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u (i.e., you do not need to check this).
eq2part :: Reln -> [[Int]]
eq2part rs = normalize [[ d | (c,d) <- rs, a == c] | (a,b) <- rs]


-- Write a function part2eq that takes a partition of u as input and returns
-- the associated equivalence relation on u. You can assume that the argument
-- is really a partition of u.
part2eq :: [[Int]] -> Reln
part2eq bs = [(a, b)| cs <- bs, a <- cs, b <- cs]
