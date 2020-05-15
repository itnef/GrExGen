{-# LANGUAGE ScopedTypeVariables, GADTs, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- Extend: compute factor morphisms for unlabeled graphs
-- Proof of concept. Not optimized. Fixes welcome of course.

module Extend where

import Prelude hiding (rem)

import Data.List

import Data.Maybe
import Control.Arrow ((&&&))
import Control.Monad
import Control.Exception(assert)
    
import Sane
import Util

import Graph
import GraphOps

failure :: MonadPlus m => m a
failure = mzero

-- Find a factor h such that g = f `o` h
-- Fails when no such a factorisation is possible. Caution: only for M-morphisms.
xetendsM' :: Morphism -> Morphism -> Morphism
xetendsM' g@(Mor srcg tgtg nmg emg) f@(Mor srcf tgtf nmf emf) =
  assert(tgtg == tgtf)$
      Mor srcg srcf
      [nmap f <. nid | nid <- nmap g]
      [emap f <. eid | eid <- emap g]

xetendsM'check :: Morphism -> Morphism -> Bool
xetendsM'check g f =
  (tgt g == tgt f) && all (`elem` nmap f) (nmap g)
                   && all (`elem` emap f) (emap g)

-- List all morphisms h such that g factorises as g = f `o` h
xetends :: Morphism -> Morphism -> [Morphism]
xetends g@Mor {} f@Mor {} =
  assert(tgt g == tgt f)$
    let nmstuff = [nmap f <.? nid | nid <- nmap g]
        emstuff = [emap f <.? eid | eid <- emap g]
    in
      [ mor
      | nm <- if v (src g) == 0 then [[]] else combinationChoices nmstuff
      , em <- if e (src g) == 0 then [[]] else combinationChoices emstuff
      , let mor = Mor (src g) (src f) nm em
      , isValidMor mor ]

-- List all morphisms q such that f = q `o` a, and q is in M (f, a need not be in M)
extendsM :: Morphism -> Morphism -> [Morphism]
extendsM (Mor srcf tgtf nmf emf) (Mor srca tgta nma ema)
  | srcf /= srca = error $ "extendsM: source mismatch " ++ show srcf ++ ", " ++ show srca
  | otherwise =
      let nm_must = nub (map ((nma .>) &&& (nmf .>)) (nodesof srca))
          em_must = nub (map ((ema .>) &&& (emf .>)) (edgesof srca))
      in
        if not (isLeftUnique nm_must) || not (isLeftUnique em_must)
        then failure
        else [ Mor tgta tgtf nme eme
             | (nme, eme) <- finish_mapping nm_must em_must (nodesof tgta)
                             (filter (`notElem`nmf) (nodesof tgtf))
                             (filter (`notElem`emf) (edgesof tgtf)) ]
        where
          finish_mapping nmp emp [] _ _ =
            [(map fromJust rnm, map fromJust rem)]
              where rnm = [lookup n nmp | n <- nodesof tgta]
                    rem = [lookup e emp | e <- edgesof tgta]

          finish_mapping nmp emp na@(n:_) remnf remef =
              case lookup n nmp of
                Nothing -> if null remnf
                             then failure
                             else
                                 concat [ finish_mapping_edges ((n,n'):nmp) emp na n' remnf' remef
                                        | (n',remnf') <- take1out remnf ]
                Just n' -> finish_mapping_edges nmp emp na n' remnf remef

          finish_mapping_edges nmp emp na@(n:natl) n' remnf remef =
              let (aes, aep) =
                      two (filter (\(e,_) -> e`notElem`map fst emp)) $
                          (successorsVia tgta &&& predecessorsVia tgta) n
                  (aes', aep') =
                      two (filter (\(e,_) -> e`elem`remef)) $
                          (successorsVia tgtf &&& predecessorsVia tgtf) n'
                  remef' = remef \\ map fst (aes' ++ aep')
              in
                if null (aes ++ aep)
                then finish_mapping nmp emp natl remnf remef'
                -- shouldn't we remove n' from remnf?
                else if lenff aes > lenff aes' || lenff aep > lenff aep'
                     then failure
                     else concat
                          [ finish_mapping nmp' (nub $ emp ++ emp'') natl remnf' remef'
                          -- (TODO: take only as many as necessary, do not permute the full list.)
                          | empchs <- nub $ map (takeff (lenff aes)) (permutations aes')
                          , empchp <- nub $ map (takeff (lenff aep)) (permutations aep')
                          , let emp'' = zip (map fst aes) (map fst empchs) ++
                                        zip (map fst aep) (map fst empchp)
                          , let nmp'' = zip (map snd aes) (map snd empchs) ++
                                        zip (map snd aep) (map snd empchp)
                          , let nmp' = nub $ nmp ++ nmp''
                          , isLeftUnique nmp'
                          , isRightUnique nmp'
                          , let remnf' = remnf \\ ([n'] ++ map snd empchs ++ map snd empchp)
                          ]

-- List all morphisms q such that f = q `o` a, not necessarily in M.
extends :: Morphism -> Morphism -> [Morphism]
extends (Mor srcf tgtf nmf emf) (Mor srca tgta nma ema)
  | srcf /= srca = error $ "extends: source mismatch " ++ show srcf ++ ", " ++ show srca
  | otherwise =
        let nm_must = map ((nma .>) &&& (nmf .>)) (nodesof srca)
            em_must = map ((ema .>) &&& (emf .>)) (edgesof srca)
        in
          [ Mor tgta tgtf nme eme | (nme, eme) <- finish_mapping nm_must em_must (nodesof tgta) ]
        where
          -- Search strategy. try incident items first (move to front of queues na / ea)
          -- (TODO: prove that it avoids checking the same mapping more than once?)
          finish_mapping nmp emp [] =
              let rnm = map (`lookup`nmp) (nodesof tgta)
                  rem = map (`lookup`emp) (edgesof tgta)
              in
                if any isNothing (rnm ++ rem) then failure else [(map fromJust rnm, map fromJust rem)]
          -- as long as there are edges in queue, try different mappings for these:
          finish_mapping nmp emp na@(n:natl) =
            case lookup n nmp of
              Nothing -> -- now the adjacent edges:
                  concat [ finish_mapping ((n,n'):nmp) emp na | n' <- nodesof tgtf ]
              Just n' ->
                  let (aes, aep) =
                          two (filter (\(eid,_) -> eid`notElem`map fst emp)) $
                                     (successorsVia tgta &&& predecessorsVia tgta) n
                      (aes', aep') = (successorsVia tgtf &&& predecessorsVia tgtf) n'
                  in case aes ++ aep of
                    [] -> finish_mapping nmp emp natl
                    _  ->
                        concat [ finish_mapping nmp' (nub $ emp ++ emp'') natl
                               | empch <-
                                   combinationChoices $
                                     takeff (lenff aes) (repeat aes') ++
                                     takeff (lenff aep) (repeat aep')
                               , let emp'' = zip (map fst (aes ++ aep)) (map fst empch)
                               , let nmp'' = zip (map snd (aes ++ aep)) (map snd empch)
                               , let nmp' = nub $ nmp ++ nmp''
                               , isLeftUnique nmp' ]
