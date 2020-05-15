{-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{- Basic functions for building and examining graphs -}

-- All extensible to hypergraphs or more general categories of graph-like algebras, in principle.
-- Instances would have to be implemented.

module Instances.GraphCategory where

import Prelude hiding (rem)

import Graph
import Sane
import Data.List(isPrefixOf, nub)

data PartialMorphism = PMor {l :: Morphism , r :: Morphism}
  deriving (Show, Read)

isValidPMor :: PartialMorphism -> Bool
isValidPMor (PMor lhs@(Mor la _ _ _)
                  rhs@(Mor ra _ _ _)) =
  isValidMor lhs && isValidMor rhs && la == ra && isInjective lhs

ø :: Graph
ø = G 0 0 [] []

idmor :: Graph -> Morphism
idmor g = Mor g g [0..v g-1] [0..e g-1]

initial :: Graph -> Morphism
initial g = Mor ø g [] []

gottaBeEq :: Morphism -> Bool
gottaBeEq m = (src m == tgt m) && nmap m `isPrefixOf` [0..] && emap m `isPrefixOf` [0..]

gottaBeIso :: Morphism -> Bool
gottaBeIso (Mor g h nm em) =
    lenff (nub nm) == lenff nm && lenff (nub em) == lenff em
    && v g == v h && e g == e h

isInjective :: Morphism -> Bool
isInjective (Mor _ _ nm em) =
    nub nm == nm && nub em == em

isMono :: Morphism -> Bool
isMono = isInjective

isIdentity :: Morphism -> Bool
isIdentity (Mor _ h nm em) =
    (nm == nodesof h) && (em == edgesof h)

composable :: Morphism -> Morphism -> Bool
composable (Mor s _ _ _) (Mor _ t' _ _) = t' == s

canonicalInclusion :: Graph -> Graph -> Morphism
canonicalInclusion g h = Mor g h (nodesof g) (edgesof g)

-- Composition of morphisms
ogm :: Morphism -> Morphism -> Morphism
ogm g@(Mor s t nm em) f@(Mor s' t' nm' em') =
  if t' /= s
     then error ("`o`: source/target mismatch, " ++ show g ++ ", " ++ show f)
     else Mor s' t (map (nm .> ) nm') (map (em .> ) em')
