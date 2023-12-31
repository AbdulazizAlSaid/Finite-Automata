import Data.List (foldl')
import Data.Char (isUpper)

-- CFG G = (Start, Follows, Nullable)
type CFG = (Char, Char -> Char -> [String], Char -> Bool)
                
accept :: CFG -> [Char] -> Bool
accept (s,d,e) = elem [] . foldl' (\xs c -> concatMap (lq c) xs) (close [s]) where  
  close [] = [""]
  close c@(x:xs) |(isUpper x) && (e x == True) = [c] ++ close xs
                 |otherwise = [c]
  lq a [] = []
  lq a (x:xs) | isUpper x = map (++ xs) $ concat $ map (close) (d x a)          -- nonterminal
              | otherwise = if a == x then [xs] else []  -- terminal
  
-- Balanced parentheses (not including the empty string)
-- original: S --> () | (S) | SS
-- in TNF:   S --> () | ()S | (S) | (S)S
  
bp :: CFG
bp = ('S', d, e) where
  d 'S' '(' = ["S)", "S)S"]
  d 'S' ')' = []
  e 'S' = True ;

-- {a^i b^j c^{i+j} | i >= 0, j > 0}
-- original: S --> aSc | T
--           T --> bTc | bc
-- in TNF:   S --> aSc | bTc | bc
--           T --> bTc | bc
  
pl = ('S', d, e) where
  d 'S' 'a' = ["Sc"]  ;  d 'S' 'b' = ["Tc","c"]  ;  d 'S' 'c' = []
  d 'T' 'a' = []      ;  d 'T' 'b' = ["Tc","c"]  ;  d 'T' 'c' = []
  e 'T' = True ;
  
--G5
--G5 - even amount of a’s and b’s
-- original: S --> aSb | bSa | SS | ε
-- in TNF: S --> aaSb | baSa | aaSS | True

g5 :: CFG
g5 = ('S', d, e) where
  d 'S' 'a' = ["bS", "aS", "b", "aSbS", "bSaS"]; d 'S' 'b' = ["bS", "aS", "a", "aSbS", "bSaS"];  
  e 'S' = True ;

--G6 
--G6 - accepts every string except empty
-- original:  S --> bS | Sa | aSb | ε 
-- in TNF: S --> abS | bSa | aSba 

g6 :: CFG
g6 = ('S',d,e) where
   d 'S' 'a' = ["bS", "bSa", "aSba", "a", "b", "aSb", "aS", ""]; d 'S' 'b' = ["bS", "bSa", "aSba", "a", "b", "aSb", "aS", ""];
   e 'S' = True ; 
   
--G2
--original: R -> F | F+R
--          F -> S | FS
--          S -> A | S*
--          A -> 0 | 1 | a1 | .. | an | (R) 
-- in TNF: R -> aaF | aaF+aaR
--         F -> aaS | aaFS
--         S -> aaA | aS*
--         A -> a0 | a1 | aa1

g2 :: CFG
g2 = ('R', d, e) where 
    d 'R' 'a' = ["aF", "bF", "baF", "aaF", "ba", "ab", ""] ; d 'R' 'b' = ["bF", "bR", "ba", "ab", ""] ;
    d 'F' 'a' = ["aS", "bS", ""] ; d 'F' 'b' = ["bFS", "aFS", "baFS", "aaFS", ""]
    d 'S' 'a' = ["aA", "bA", "", "abA", "bbA"] ; d 'S' 'b' = ["bS*", "aS*", "", "a", "b", "ba", "ab"] ;
    d 'A' 'a' = ["", "a", "b", "ba", "ab", "bAa", "aAa"] ;
    e 'R' = True ;
 