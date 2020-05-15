{-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{- Basic functions for building and examining graphs,
   using the simple representation from Graph module -}

-- In principle, these functions are extensible to hypergraphs
-- or more general categories of graph-like algebras.

module GraphOps where

import Prelude hiding (rem)

import Data.List

import Control.Arrow ((&&&))
import qualified Data.Set as S
import Control.Exception(assert)
    
import Sane
import Util

import Graph
import Instances.GraphCategory

isStronglyConnected :: Graph -> Bool
isStronglyConnected = (<=1) . lenff . scc

edgerev :: Graph -> Graph
edgerev (G vu eu veu evu) = G vu eu evu veu

cc :: Graph -> [S.Set Nid]
cc = scc . symmetrize

symmetrize :: Graph -> Graph
symmetrize (G vu eu veu evu) = G vu (eu+eu) (veu++evu) (evu++veu)

-- Outputs the sets of nodes that induce the strognly connected components of the graph.
scc :: Graph -> [S.Set Nid]
scc g = scc' (S.fromList (nodesof g)) where
  scc' toExplore | S.null toExplore = []
  scc' toExplore =
    let (n, _) = S.deleteFindMin toExplore
        x = tsucc g n
    in
      if n ∈ x
      then x : scc' (S.difference toExplore x)
      else S.singleton n : scc' (S.difference toExplore (S.singleton n))

-- (TODO: could also record (some) shortest paths)
tsucc :: Graph -> Nid -> S.Set Nid
tsucc g n =
  S.unions [ rtsucc' S.empty g (S.singleton n') | n' <- successors g n ]

rtsucc' :: S.Set Nid -> Graph -> S.Set Nid -> S.Set Nid
rtsucc' accum g sn
         | S.null sn = accum
         | otherwise = let (n, t) = S.deleteFindMin sn
                       in
                         if n ∈ accum
                         then rtsucc' accum g t
                         else
                             let ss = successorset g n
                             in  rtsucc' (accum ∪ S.singleton n) g (t ∪ ss)

tsuccVia :: Graph -> Nid -> S.Set ([Eid],Nid)
tsuccVia g n = S.delete ([], n) (rtsuccVia g n)

rtsuccVia :: Graph -> Nid -> S.Set ([Eid],Nid)
rtsuccVia g n =
  rtsuccVia' S.empty (S.singleton ([],n)) g 
              (S.fromList (map (\(x,y) -> (n,x,y)) (successorsVia g n)))

rtsuccVia' :: S.Set Nid -> S.Set ([Eid],Nid) -> Graph -> S.Set (Nid,Eid,Nid) -> S.Set ([Eid],Nid)
rtsuccVia' reached accum g sn
  | S.null sn = accum
  | otherwise =
    let ((nfrom, via, n), t) = S.deleteFindMin sn
    in  if n ∈ reached
        then rtsuccVia' reached accum g t
        else let svia = successorsVia g n
             in  rtsuccVia' (reached ∪ S.singleton n)
                         (accum ∪ S.map
                                    (\(path,_) -> (path++[via], n))
                                    (S.filter (\(_,n'') -> n'' == nfrom) accum))
                         g (t ∪ S.fromList (map (\(x,y) -> (n,x,y)) svia))

-- Partial function, node IDs must exist (i.e. be <v)
addEdge :: (Nid, Nid) -> Graph -> Graph
addEdge (n1,n2) (G v e ve ev)
  | n1 >= v || n2 >= v = error "addEdge: out of range"
  | otherwise = G v (e+1) (ve++[n1]) (ev++[n2])

addNode :: Graph -> Graph
addNode (G v e ve ev) = G (v+1) e ve ev

addAndReturnNewNode :: Graph -> (Graph, Nid)
addAndReturnNewNode (G v e ve ev) = (G (v+1) e ve ev, v)

addEdgemor :: (Nid,Nid) -> Graph -> Morphism
addEdgemor (n1,n2) (G v e ve ev)
  | n1 >= v || n2 >= v = error "addEdgemor: out of range"
  | otherwise = Mor (G v e ve ev)
                    (G v (e+1) (ve++[n1]) (ev++[n2]))
                    [0..v-1]
                    [0..e-1]

-- --*-- -- sample graphs -- --*-- --

-- Cycle graphs directed-C_n
grcycle :: Integer -> Graph
grcycle 0 = ø
grcycle n = G n n [0..n-1] ([1..n-1]++[0])

-- discrete graph
grdiscrete :: Integer -> Graph
grdiscrete n = G n 0 [] [] 

-- chain graph
grchain :: Integer -> Graph
grchain 0 = ø
grchain n = G n (n-1) [0..n-2] [1..n-1]

-- unlabeled flower graph
flower :: Integer -> Graph
flower n = G 1 n (takeff n (repeat 0)) (takeff n (repeat 0))

-- unlabeled star graph
star :: Integer -> Graph
star n = G (1+n) n (takeff n (repeat 0)) [1..n]

-- for grid
edgeMerge :: Graph -> Graph -> Graph
edgeMerge g1 g2 = assert (v g1 == v g2) $
              G (v g1) (e g1 + e g2) (ve g1 ++ ve g2) (ev g1 ++ ev g2)

completebi :: Integer -> Graph
completebi n = foldr addEdge (grdiscrete n) [ (i,j) | i <- [0..n-1], j <- [0..n-1], i /= j ]

-- grid, top left to down right
-- 0 1 2 .. n-1 \n n n+1 n+2 .. 
grid :: Integer -> Integer -> Graph
grid m n = edgeMerge 
  ( foldr addEdge (grdiscrete (m * n)) [ (i,j) | x <- [0..n-1], y <- [0..m-2]
                                       , let i = x + y * n
                                       , let j = x + (y + 1) * n
                                       ] )
  ( foldr addEdge (grdiscrete (m * n)) [ (i,j) | x <- [0..n-2], y <- [0..m-1]
                                       , let i = x + y * n
                                       , let j = x + 1 + y * n
                                       ] )

-- Disjoint union
disjun :: Graph -> Graph -> Graph
disjun (G v e ve ev) (G v' e' ve' ev') = G (v+v') (e+e') (ve++map (+v) ve') (ev++map (+v) ev')

newtype BrokenGraph = BrokenGraph {unbroken::Graph}
broken :: Graph -> BrokenGraph
broken = BrokenGraph

(+-+) :: BrokenGraph -> BrokenGraph -> BrokenGraph
(+-+) (BrokenGraph (G vu eu veu evu))
      (BrokenGraph (G v' e' ve' ev')) =
       BrokenGraph (G (vu+v') (eu+e') (veu++ve') (evu++ev'))

restrict :: (Nid -> Bool) -> (Eid -> Bool) -> Graph -> Maybe Graph
restrict vf ef g =
  let vs' = filter vf (nodesof g)
      es' = filter ef (edgesof g)
      g' = G (lenff vs') (lenff es')
           (map ((vs'.>) . (ve g.>)) es')
           (map ((vs'.>) . (ev g.>)) es')
      valid = all (`elem`vs') (map (ve g.>) es' ++ map (ev g.>) es')
  in
    if valid then Just g' else Nothing

{- Deprecated. Use pushouts instead. -}
jun :: Nid -> Eid -> Graph -> Graph -> Graph
jun nv ne g@(G vg eg veg evg) g'@(G v' e' ve' ev') =
  let rg1 = restrict (<nv) (<ne) g
      rg2 = restrict (<nv) (<ne) g'
  in
  case (rg1, rg2, rg1 == rg2) of
    (Just _, Just _, True) -> 
      G (vg+v'-nv)
        (eg+e'-ne)
        (veg ++ map (\nid -> if nid<nv then nid else nid+vg-nv) (dropff ne ve'))
        (evg ++ map (\nid -> if nid<nv then nid else nid+vg-nv) (dropff ne ev'))
    _  -> error $ "jun: invalid " ++ show g ++ "," ++ show g'

junsr :: Nid -> Eid -> [Graph] -> Graph
junsr _ _ [] = ø
junsr nv ne (h:t) = foldr (jun nv ne) h t

junsl :: Nid -> Eid -> [Graph] -> Graph
junsl _ _ [] = ø
junsl nv ne (h:t) = foldl (jun nv ne) h t

juns :: Nid -> Eid -> [Graph] -> Graph
juns = junsr

loops :: Graph -> [Eid]
loops g = filter (uncurry (==) . srctgt g) (edgesof g)

loopsByNode :: Graph -> [[Eid]]
loopsByNode g =
    [ es | n <- nodesof g
         , let es = [ eid | (eid,n') <- successorsVia g n , n == n' ] ]

parallelEdges :: Graph -> [((Nid,Nid), [Eid])]
parallelEdges g =
  if e g == 0 then [] else
   map (\(h:t) -> (fst h , map snd (h:t))) $
      groupSortBy fst $
      map (\eid -> (srctgt g eid, eid)) (edgesof g)

-- recomputed ...
edgesBetween :: Graph -> Nid -> Nid -> [Eid]
edgesBetween g ni nj =
  filter ((==(ni,nj)) . srctgt g) (edgesof g)

successors :: Graph -> Nid -> [Nid]
successors (G _ _ ve ev) x =
  applyRelToSet (zip ve ev) [x]

successorset :: Graph -> Nid -> S.Set Nid
successorset g x =
  S.fromList ( successors g x )

successorsVia :: Graph -> Nid -> [(Eid,Nid)]
successorsVia (G _ _ ve ev) x =
  applyRelToSet (zip ve (zip [0..] ev)) [x]

predecessors :: Graph -> Nid -> [Nid]
predecessors (G _ _ ve ev) x =
  applyRelToSet (zip ev ve) [x]

predecessorsVia :: Graph -> Nid -> [(Eid,Nid)]
predecessorsVia (G _ _ ve ev) x =
  applyRelToSet (zip ev (zip [0..] ve)) [x]

neighbours :: Graph -> Nid -> [Nid]
neighbours g x = predecessors g x ++ successors g x

adjacentEdges :: Graph -> Nid -> [(Eid,[Nid])]
adjacentEdges g x =
  [(i,[j,k]) | i <- [0..e g-1] , let j = ve g .> i ; k = ev g .> i , j == x || k == x]

-- Don't ask questions; embed.
embed :: Graph -> Graph -> Morphism
embed = canonicalInclusion

-- Invert an isomorphism
inv :: Morphism -> Morphism 
inv y@(Mor s t nm em)
  | not (gottaBeIso y) = error "inv: not iso"
  | otherwise = Mor t s (inversePerm nm) (inversePerm em)

-- Diagnostics for debugging
reasonInvalidPMor (PMor l r) =
  (not (isValidMor l), not (isValidMor r))

reasonInvalidMor (Mor src tgt nmap emap) =
  (fiff (>=v tgt) nmap, fiff (>=e tgt) emap,
   not (isValidG src),  not (isValidG tgt),
   lenff emap /= e src, lenff nmap /= v src,
   fiff (\eid -> nmap .> (ev src .> eid) /= ev tgt .> (emap .> eid) ||
                 nmap .> (ve src .> eid) /= ve tgt .> (emap .> eid) ) [0 .. e src - 1])

-- Output: (in-degree, out-degree)
degree :: Graph -> Nid -> (Integer, Integer)
degree g@(G v e ve ev) n = (c ve, c ev)
  where c ls = sum [1 | _ <- filter (==n) ls]

hasNoIsolatedNodes :: Graph -> Bool
hasNoIsolatedNodes g =
  all (\x -> elem x (ve g) || elem x (ev g)) (nodesof g)

hasNoLoops :: Graph -> Bool
hasNoLoops gr@(G _ e _ _) =
  all (uncurry (/=) . srctgt gr) [0 .. e-1]

-- implement isomorphism checks?
