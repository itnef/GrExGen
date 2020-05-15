{- (Big)Integer based replacements for the Int-based standard library functions. genericLength and so on are now part of Prelude. but their names are a bit too long. -}
module Sane where

import Control.Arrow

import Text.Printf

import qualified Data.Set as S
import qualified Data.List as L ((\\))

saneSize :: S.Set a -> Integer
saneSize = lenff . S.toList

-- Less incorrect list length function, = genericLength
lenff :: [a] -> Integer
lenff = foldr (\_ -> (+) 1) 0

splitAtff :: Integer -> [a] -> ([a],[a])
splitAtff i w | i < 0 || i > lenff w = error (printf "splitAtff: index %d " i)
splitAtff i w = splitAtff' i w [] where
  splitAtff' 0 w v = (v,w)
  splitAtff' i (h:t) u = splitAtff' (i-1) t (u++[h])

-- Integer-based version of (!!)
atff :: [a] -> Integer -> a
atff _ x | x < 0 = error $ "atff: index "++show x++" negative"
atff [] x        = error $ "atff: index "++show x++" too large"
atff (h:_) 0 = h
atff (_:t) x = atff t (x-1)

(.>) :: [a] -> Integer -> a
(.>) = atff
infixl 7 .>

-- lookup two elements
atff2 :: [a] -> (Integer, Integer) -> (a, a)
atff2 ls = (***) (ls .>) (ls .>)

-- Why aren't infix precedences rational numbers?
(..>) :: [a] -> [Integer] -> [a]
(..>) l = map (l.>)
infixl 8 ..>

-- Caution, will diverge on infinite lists.
(!.>) :: [a] -> [Integer] -> [a]
ls !.> ixs = ls ..> ([0..lenff ls-1] L.\\ ixs)
infix 8 !.>

atffs :: [a] -> [Integer] -> [a]
atffs = (..>) 

-- Replacement for findIndices
fiff :: (a -> Bool) -> [a] -> [Integer]
fiff f ls = fiff' ls 0 where
  fiff' [] _    = []
  fiff' (h:t) n | f h = n:fiff' t (n+1)
  fiff' (_:t) n       =   fiff' t (n+1)

-- Fails if no satisfying element exists
firstindex :: (Eq a) => a -> [a] -> Integer
firstindex x = head . fiff (==x)

-- Like Prelude.take
takeff :: Integer -> [a] -> [a]
takeff i _ | i < 0 = error "takeff: index negative"
takeff _ [] = []
takeff 0 _ = []
takeff i (h:t) = h : takeff (i-1) t

-- Like Prelude.drop
dropff :: Integer -> [a] -> [a]
dropff i _ | i < 0 = error "dropff: index negative"
dropff _ [] = []
dropff 0 ls = ls
dropff i (_:t) = dropff (i-1) t
