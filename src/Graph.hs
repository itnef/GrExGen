{- Basic representation of unlabeled graphs. -}

module Graph where

import Sane
import Util
import Data.Maybe

import Control.Arrow ((&&&))

import Text.Printf -- for prettyPrintMor

-- Edge, node numbers within a graph. The sets are always represented as prefixes of \mathbb{N}.
type Eid = Integer
type Nid = Integer

-- A very basic and unoptimised representation.
data Graph = G
  {v :: Integer, e :: Integer, ve :: [Nid], ev :: [Nid]}
  deriving (Eq, Show, Read, Ord)

data Morphism = Mor
  {src :: Graph, tgt :: Graph, nmap :: [Nid], emap :: [Eid]}
  deriving (Eq, Show, Read, Ord)

-- Accessors:
nodesof :: Graph -> [Nid]
nodesof g = [0..v g-1]

edgesof :: Graph -> [Eid]
edgesof g = [0..e g-1]

srctgt :: Graph -> Eid -> (Nid,Nid)
srctgt g = (ve g .>)&&&(ev g .>)

isValidG :: Graph -> Bool
isValidG (G v e ve ev) =
  not (any (\(eid,nid) -> eid >= e || nid >= v) (zip [0..] ev)) &&
  not (any (\(nid,eid) -> eid >= e || nid >= v) (zip ve [0..])) &&
  all (\eid -> isJust (rookup eid (zip ve [0..]))) [0..e-1] &&
  all (\eid -> isJust (lookup eid (zip [0..] ev))) [0..e-1] &&
  isLeftUnique (zip [0::Integer ..] ev)
  && isRightUnique (zip ve [0::Integer ..])

isValidMor :: Morphism -> Bool
isValidMor (Mor src tgt nmap emap) =
   isValidG src &&
   isValidG tgt &&
   not (any (>= v tgt) nmap) && not (any (>= e tgt) emap) &&
   (lenff emap == e src)     && (lenff nmap == v src) &&
   all (\eid -> nmap .> (ev src .> eid) == ev tgt .> (emap .> eid) &&
                nmap .> (ve src .> eid) == ve tgt .> (emap .> eid) ) [0 .. e src - 1] 

prettyPrintMor :: IsChar a => Morphism -> [a]
prettyPrintMor (Mor (G v e ve ev) (G v' e' ve' ev') nm em) =
  printf "Mor from  %d %d %s %s\n" v e (show ve) (show ev) ++ 
  printf "      to  %d %d %s %s\n" v' e' (show ve') (show ev') ++ 
  printf "    nmap  %s\n" (show nm) ++
  printf "    emap  %s\n" (show em)
