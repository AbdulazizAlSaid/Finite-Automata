-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3


---------------- Code provided to you in Lab 3 ----------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('0':xs) rs         = go xs (Empty:rs)
  go ('1':xs) rs         = go xs (Star Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


---------------- Your solution to Lab 3 ----------------

-- Include here any code you need from your solution to Lab 3 for testing
-- purposes. After a few days, I will release a solution for you to use.
-- Don't duplicate the code just given above.
cart :: [a] -> [b] -> [(a,b)]
cart xs ys = [ (a,b) | a <- xs, b <- ys]

-- Powerset, preserves normalization
power :: [a] -> [[a]]
power [] = [[]]
power [x] = [[], [x]]
power (x:xs) = [[]] ++ [ [h] ++ hs | h <-[x], hs <- power xs ] ++ tail(power xs)

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot xs (LOL 0 _) = xs   -- Not needed, but makes kstar more efficient
dot (LOL x xs) (LOL y ys) = (LOL (x+y) (xs++ys))

-- Reverse of LOLs, preserves invariant
rev :: LOL a -> LOL a
rev (LOL n (x:xs)) = ( LOL n (reverse xs ++ [x]))

-- Merge of langages (aka "union")
merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] [] = []                    
merge (x:xs) [] = (x:xs) ++ []      
merge [] (y:ys) = (y:ys) ++ []      
merge (x:xs) (y:ys) 
  | (x) < (y) = (x) : (merge (xs) (y:ys))
  | (x) > (y) = (y) : (merge (x:xs) (ys))
  | otherwise = (x) : (merge (xs) (ys))  

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat (x:xs) (y:ys) = [dot x y] ++ 
 merge ([ dot n r | n<- [x], r<- ys]) ([dot a b | a <- xs, b <- (y:ys) ])

-- Left quotient of a language by a string
leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq _ [] = []
leftq w@(LOL n xs) (LOL m ys:yss) =
  case stripPrefix xs ys of
    Nothing -> leftq w yss
    Just zs -> LOL (m-n) zs : leftq w yss

-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)

-- The language associated to a regular expression, i.e., [[r]]
lang_of :: RegExp -> Lang Char
lang_of Empty = []
lang_of (Let a) = lang [[a]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)

-- The one-string and finite languages of Theorem 3.2.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr [x] = Let x
onestr (x:xs) = Cat (Let x) (onestr xs)

finite :: [String] -> RegExp
finite [] = Empty
finite [w] = onestr w
finite (w:ws) = Union (onestr w) (finite ws)

memb :: Ord a => LOL a -> Lang a -> Bool
memb (LOL n ys) [] = False
memb (LOL n ys) (x:xs) 
  | (LOL n ys) > x = memb (LOL n ys) (xs)
  | (LOL n ys) == x = True
  | otherwise = False;


---------------- Part 1 ----------------

-- Implement the seven RECURSIVE predicates/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, uni, byp, inf, revrs, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function. Then implement one more not given there: purity.
empty :: RegExp -> Bool
empty (Empty) = True
empty (Let a) = False
empty (Union r1 r2) = (empty(r1)) && (empty(r2))
empty (Cat r1 r2) = (empty(r1)) || (empty(r2))
empty (Star r) = False

uni :: RegExp -> Bool
uni (Empty) = False
uni (Let a) = False
uni (Union r1 r2) = (empty(r1) && uni(r1)) || (uni(r1) && empty(r2)) || (uni(r1) && uni(r2))
uni (Cat r1 r2) = (uni(r1)) && (uni(r2))
uni (Star r) = (empty(r)) || (uni(r))

byp :: RegExp -> Bool
byp (Empty) = False
byp (Let a) = False
byp (Union r1 r2) = (byp(r1)) || (byp(r2))
byp (Cat r1 r2) = (byp(r1)) && (byp(r2))
byp (Star r) = True

inf :: RegExp -> Bool
inf (Empty) = False
inf (Let a) = False
inf (Union r1 r2) = (inf(r1)) || (inf(r2))
inf (Cat r1 r2) = ((inf(r1)) && not (empty(r2))) || ((inf(r2)) && not (empty(r1))) 
inf (Star r) = not (empty(r)) && not (uni(r))

revers :: RegExp -> RegExp
revers (Empty) = Empty
revers r1 = r1
revers (Let a) = Let a
revers (Union r1 r2) = (Union(revers(r1)) (revers(r2)))
revers (Cat r1 r2) =  (Cat (revers(r2)) (revers(r1)))
revers (Star r) = Star (revers r)

lq :: Char -> RegExp -> RegExp
lq s (Empty) = Empty
lq s (Let a) 
  | s == a = (Star (Empty))
  | otherwise = Empty
lq s (Union r1 r2) = Union (lq s r1) (lq s r2)
lq s (Cat r1 r2) 
  | byp (r1) = Union (Cat (lq s r1) r2) (lq s r2)
  | otherwise = Cat (lq s r1) r2
lq s (Star r1) = Cat (lq s r1) (Star r1)

nep :: RegExp -> RegExp 
nep (Empty) = Empty
nep (Let a) = Let a
nep (Union r1 r2) = (Union (nep(r1)) (nep(r2)))
nep (Cat r1 r2) 
  | byp r1 = Union (Cat (nep r1) r2) (nep r2)
  | otherwise = Cat (nep (r1)) (r2)
nep (Star r) =  Cat (nep (r)) (Star r)

-- Purity. A regular expression is *pure* if every string matching r
-- has at least one character, or, equivalently, if ε is not in [[r]].
-- (Note that r is pure exactly when r is not bypassable, but you are
-- to give a recursive definition here, not define it in terms of byp.)

purity :: RegExp -> Bool
purity (Empty) = not False
purity (Let a) = not False
purity (Union r1 r2) = not ((purity(r1)) || (purity(r2)))
purity (Cat r1 r2) = not ((purity(r1)) && (purity(r2)))
purity (Star r) = not True

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "bc" =  [("","bc"), ("b","c"), ("bc","")]
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = [ (take r list, drop r list) | r<- [0..length xs], list <- [xs] ]

match1 :: RegExp -> String -> Bool
match1 Empty w = False
match1 (Let a) w 
  | (length w == 1) = (Let a == (toRE w))
  | otherwise = False
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = or [(match1 r1 w1) && (match1 r2 w2) | (w1, w2) <- splits w]
match1 (Star r1) w =  (null w) || or[(match1 r1 w1) && (match1 (Star r1) w2) | (w1,w2) <- splits w, not(null w1)]



-- Helper function
match2' :: [RegExp] -> Bool -> String -> Bool
match2' r b w | null r = null w
match2' ((Empty):rs) b w = False
match2' ((Let x):rs) b w 
  | length w >= 1 = (Let x == toRE [head w]) && match2' rs False (tail(w))
  | otherwise = False
match2' ((Union r1 r2):rs) b w = match2' (r1:rs) b w || match2' (r2:rs) b w
match2' ((Cat r1 r2):rs) b w = match2' (r1:r2:rs) b w || b && byp(r1) && match2'(r2:rs) True w
match2' ((Star r1):rs) b w = not b && (match2' rs False w || match2' (r1:(Star r1):rs) True w)

match2 :: RegExp -> String -> Bool
match2 r w = match2' (r:[]) False w



-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concatMap str [0..n] where
  str 0 = [""]
  str n = [a:w | a <- sigma, w <- str (n-1)]
