{-# LANGUAGE KindSignatures, FlexibleContexts, RankNTypes, LambdaCase #-}

{- Filled small gaps in the standard library, notational preferences -}

module Util where

import Sane
import Data.Either()
import Data.List (groupBy,sortBy,minimumBy,nub,sort,(\\))
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad.Writer
import Control.Arrow ((***), Arrow, first, second)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Function (on)

import GHC.IO.Exception (ExitCode(ExitSuccess))

import Debug.Trace

traceshow :: Show a1 => a1 -> a -> a
traceshow x = trace (show x)
traceShow :: Show a1 => a1 -> a -> a
traceShow = traceshow

replace :: [a] -> Integer -> a -> [a]
replace ls i x = ( ls ..> [0..i-1] ) ++ [x] ++ ( ls ..> [i+1..lenff ls -1])

unplace :: [a] -> Integer -> [a]
unplace ls i = ( ls ..> [0..i-1] ) ++ ( ls ..> [i+1..lenff ls -1])

unplaces :: [a] -> [Integer] -> [a]
unplaces ls ixs = ls ..> ([0..lenff ls-1] \\ ixs)
(..>!) :: [a] -> [Integer] -> [a]
(..>!) = unplaces
infixl 7 ..>!

nany :: (a -> Bool) -> [a] -> Bool
nany = curry ( not . uncurry any )

anyAtAll :: [a] -> Bool
anyAtAll = not . null

suffixes :: [a] -> [[a]]
suffixes [] = [[]]
suffixes (h:t) = (h:t) : suffixes t

properSuffixes :: [a] -> [[a]]
properSuffixes []    = []
properSuffixes (_:t) = suffixes t

prefixes :: [a] -> [[a]]
prefixes = map reverse . suffixes . reverse

properPrefixes :: [a] -> [[a]]
properPrefixes = map reverse . properSuffixes . reverse

{- Chain shell commands like && -}
(&&&&) :: forall (m :: * -> *) . Monad m => m ExitCode -> m ExitCode -> m ExitCode
(&&&&) a b = a >>= \case ExitSuccess -> b; x -> return x

infixl 1 &&&&

splits :: [a] -> [([a],[a])]
splits [] = [([],[])]
splits ls@(h:t) = ([],ls) : map (first (h:)) (splits t)

compose :: [b -> b] -> b -> b
compose = foldr (.) id

fsts :: [(a, b)] -> [a]
fsts = map fst
snds :: [(a, b)] -> [b]
snds = map snd

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a
snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b
þrd3 :: (a,b,c) -> c
þrd3 (_,_,c) = c

compareBy :: (Ord b) => (a -> b) -> (a -> a -> Ordering)
compareBy f x y = compare (f x) (f y)

(∈) :: forall a. Ord a => a -> S.Set a -> Bool
a ∈ b = S.member a b
infix 4 ∈

(∉) :: forall a. Ord a => a -> S.Set a -> Bool
a ∉ b = not (a ∈ b)
infix 4 ∉

(∪) :: forall a. Ord a => S.Set a -> S.Set a -> S.Set a
a ∪ b = S.union a b
infixl 5 ∪

(⊆) :: forall a. Ord a => S.Set a -> S.Set a -> Bool
a ⊆ b = S.isSubsetOf a b
infix 5 ⊆

-- We use this symbol for initial objects already.
-- ø :: forall a. (Ord a) => S.Set a
-- ø = S.empty

-- Internally a map is just a tree and costly conversions should be unnecessary??
keysSet :: (Ord k) => M.Map k v -> S.Set k
keysSet = S.fromList . M.keys

lookupDefault :: (Ord k) => v -> M.Map k v -> k -> v
lookupDefault x m k =
  fromMaybe x (M.lookup k m)

minBy :: (Ord b) => (a -> b) -> [a] -> a
minBy f = minimumBy (compare `on` f) 

numDistinct :: Eq a => [a] -> Integer
numDistinct = lenff . nub
justLookupIn :: Eq b => [(b, a)] -> b -> a
justLookupIn ls n = fromJust(lookup n ls)
justLookupMap :: (Ord a) => M.Map a b -> a -> b
justLookupMap x n = fromJust(M.lookup n x)

chaincompare :: Ord a => a -> a -> Ordering -> Ordering
chaincompare a a' b = case compare a a' of { LT -> LT ; GT -> GT ; EQ -> b }

lookupIn :: Eq a => [(a, b)] -> a -> Maybe b
lookupIn = flip lookup

applyRelToSet :: (Eq a) => [(a,b)] -> [a] -> [b]
applyRelToSet xys zs = [y | z <- zs , (x,y) <- xys , x == z]

updateInList :: [a] -> Integer -> (a -> a) -> [a]
updateInList _ n _ | n<0 = error "updateInList: negative index(!)"
updateInList [] _ _      = error "updateInList: wrong index"
updateInList (h:t) 0 e = e h : t
updateInList (h:t) n e = h: updateInList t (n-1) e

rectify :: [Integer] -> [Integer]
rectify ls =
  map (`firstindex`nub ls) ls

-- Use with special syntax highlighting rule:
nyi :: a
nyi = error "not yet implemented"

two :: Control.Arrow.Arrow a =>
       a b' c' -> a (b', b') (c', c')
two f = f *** f

neither :: [Bool] -> Bool
neither = all not
pam     :: [a] -> (a -> b) -> [b]
pam     = flip map
swap :: (a, b) -> (b, a)
swap (x,y) = (y,x)

-- like lookup, but with swapped order ;-)
rookup :: Eq a => a -> [(b, a)] -> Maybe b
rookup x ls = lookup x (map swap ls)

(<..) :: Eq a => [a] -> [a] -> [Integer]
(<..) x = map (x <.)

(<.) :: (Eq a) => [a] -> a -> Integer
(<.) ls n = head $ fiff (==n) ls
infixl 7 <.

findfirst :: (a -> Bool) -> [a] -> Integer
findfirst predicate ls =
  head $ fiff predicate ls

(<.?) :: (Eq a) => [a] -> a -> [Integer]
(<.?) ls n = fiff (==n) ls
infixl 6 <.?

-- Relations between {0, ..., n}-sets represented as lists
composeIRel :: [Integer] -> [Integer] -> [Integer]
composeIRel x y = map (y .>) x

-- more list functions

nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy _ [] = []
nubBy comp (h:t) = h: nubBy comp (filter (not . comp h) t)

combinationChoices :: [[a]] -> [[a]]
combinationChoices [] = []
combinationChoices [l] = map return l
combinationChoices (h:tl) =
  concatMap (\h' -> map (h':) (combinationChoices tl)) h

take1out :: [a] -> [(a,[a])]
take1out [] = error "take1out: empty list"
take1out [h] = [(h,[])]
take1out (h:t) =
    (h,t) : map (second (h:)) (take1out t)

allDifferent :: Eq a => [a] -> Bool
allDifferent ls = lenff ls == lenff (nub ls)

-- Use only if you can prove convergence ...
fixIter :: (Eq a) => (a -> a) -> a -> a
fixIter f x =
  let fx = f x
  in
    if fx == x
    then x
    else fixIter f fx

-- fixIter, where an extra stream can be read.
fixIterWithStream :: (Eq a) => [b] -> (b -> a -> a) -> a -> a
fixIterWithStream (h:t) f x =
  let fx = f h x
  in
    if fx == x
    then x
    else fixIterWithStream t f fx

-- fixIter, where an extra stream can be read, and custom comparison
fixIterByiWithStream :: (b -> a -> a -> Bool) -> [b] -> (b -> a -> a) -> a -> a
fixIterByiWithStream criterion (h:t) f x =
  let fx = f h x
  in
    if criterion h x fx
    then x
    else fixIterByiWithStream criterion t f fx

scanFixIter :: (Eq a) => (a -> a) -> a -> [a]
scanFixIter f x0 =
  auxf x0 []
  where
    auxf x accum =
      let fx = f x
      in
        if fx == x
        then x:accum
        else auxf fx (x:accum)

-- Monitor progress
scanFixIterMon :: (Eq a, Show x) => (a -> x) -> (a -> a) -> a -> Writer [x] [a]
scanFixIterMon sho f x0 =
  auxf x0 []
  where
    auxf x accum = do
      tell [sho x]
      let fx = f x
      if fx == x
      then return (x:accum)
      else auxf fx (x:accum)

-- No groupBy without its sortBy
groupSortBy :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortBy f = groupBy ((==) `on` f) . sortBy (compare `on` f)

-- Invert a permutation given as list of target indices
inversePerm :: [Integer] -> [Integer]
inversePerm ls = concatMap (\i -> fiff (==i) ls) [0..lenff ls]

sortnub :: Ord a => [a] -> [a]
sortnub = nub . sort
sortNub :: Ord a => [a] -> [a]
sortNub = sortnub

sortNubBy :: Ord a => (a -> a -> Ordering) -> [a] -> [a]
sortNubBy comp = nubBy (\x y -> case comp x y of EQ -> True; _ -> False) . sortBy comp

-- Remove the elements with the given indices from a list.
-- Ignores out-of-bound indices.
deliff :: [a] -> [Integer] -> [a]
deliff w is = aux 0 w (sortnub is) where
 aux _ [] _ = []
 aux _ w [] = w
 aux i (h:t) (hi:ti)
   | i == hi = aux (i+1) t ti
   | hi < i  = aux i (h:t) ti
   | hi > i  = h:aux (i+1) t (hi:ti)
-- Will not work on infinite lists, becaue it involves sortnub.

-- Only finite lists
keepiff :: [a] -> [Integer] -> [a]
keepiff ls is = deliff ls ([0..lenff ls-1] \\ is)

-- Output as ROMAN numerals
lromanif :: Integer -> String
lromanif n
  | abs n >= 10000 = show n
  | otherwise = lroman n
lroman :: Integer -> String
lroman n
  | n == 0 = show n
  | n < 0 = "-" ++ lroman (-n)
  | n == 999 = "im"
  | n == 99 = "ic" -- isn't it?
  | n >= 1000 = let (q,r) = n`divMod`1000 in takeff q (repeat 'm') ++ if r==0 then "" else lroman r
  | n >= 100 = let (q,r) = n`divMod`100 in (if q==9 then "cm" else if q>=5 then 'd':takeff (q-5) (repeat 'c') else if q==4 then "cd" else takeff q (repeat 'c')) ++ if r==0 then "" else lroman r
  | n >= 10 = let (q,r) = n`divMod`10 in (if q==9 then "xc" else if q>=5 then 'l':takeff (q-5) (repeat 'x') else if q==4 then "xl" else takeff q (repeat 'x')) ++ if r==0 then "" else lroman r
  | otherwise = if n == 9 then "ix" else if n >= 5 then 'v':takeff (n-5) (repeat 'i') else if n == 4 then "iv" else takeff n (repeat 'i')

-- -* Relations *- --
-- Applies to relations represented as lists of pairs
isLeftUnique :: Eq a => [(a,b)] -> Bool
isLeftUnique ls = length (nub (map fst ls)) == length ls
isRightUnique :: Eq a => [(b,a)] -> Bool
isRightUnique ls = length (nub (map snd ls)) == length ls

-- Symmetric difference
(/\) :: (Eq a) => [a] -> [a] -> [a]
(/\) ks ls = ks \\ (ks \\ ls)
