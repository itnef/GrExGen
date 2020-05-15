{-# LANGUAGE ScopedTypeVariables, MultiParamTypeClasses #-}

-- Some generic constructions for (M-)adhesive categories. => see Adhesive.hs,

{- Instance of Adhesive Categories: Graph+Morphism -}

-- missing feature: general pushout complements are not implemented.

module Instances.GraphAdhesive where

import Control.Exception.Base (assert)

import Util
import Sane

import Graph
import Category.Category
import Category.Adhesive
import qualified Instances.GraphCategory as G

import GraphOps

import Data.List (nub, intersect)
import Control.Arrow
import Text.Printf

import qualified Data.Set as S

instance Category Graph Morphism where
    idmor = G.idmor
    o     = G.ogm
    srcm  = src
    tgtm  = tgt

instance CatExtra Graph Morphism where
    isIdmor    = G.isIdentity
    inv f      = assert (G.gottaBeIso f) (GraphOps.inv f)
    isMono     = G.isMono
    isIso      = G.gottaBeIso
    isEq       = G.gottaBeEq
    areJS      = areJS_g 
    composable = G.composable

instance Adhesive Graph Morphism where
    pullback  = gPullback
    pushout   = gPushout
    initial   = G.initial
    hPullback = hPullback_g
    hPushout  = hPushout_g
    pocM      = pocM_g
    ø _       = G.ø
    øhelper   = initial G.ø

showpocMsof :: (Morphism, Morphism) -> IO [[()]]
showpocMsof (f,g') =
  let res = pocMsof (f,g') in
     sequence
     [ mapM (putStr . prettyPrintMor) [f,g,f',g'] | (_,g,f',_) <- res ]

isValidSpan :: (Morphism, Morphism) -> Bool
isValidSpan (Mor srca _ _ _ , Mor srcb _ _ _) =
  srca == srcb
isValidCoSpan :: (Morphism, Morphism) -> Bool
isValidCoSpan (Mor _ tgta _ _ , Mor _ tgtb _ _) =
  tgta == tgtb

isJointlySurjective :: CoSpan Morphism -> Bool
isJointlySurjective (f,g)
  | tgt f /= tgt g = error ("Jointly surj.: target mismatch, " ++ show (tgt f, tgt g))
isJointlySurjective (f,g) = let tgtf = tgt f in
  v tgtf == numDistinct (map (nmap f .>) (nodesof (src f)) ++ map (nmap g .>) (nodesof (src g))) &&
  e tgtf == numDistinct (map (emap f .>) (edgesof (src f)) ++ map (emap g .>) (edgesof (src g)))

isValidCommutingSquare :: (Morphism,Morphism,Morphism,Morphism) -> Bool
isValidCommutingSquare (f,g,f',g') =
    (src f == src g) &&
    (tgt f == src g') &&
    (tgt g == src f') &&
    (tgt f' == tgt g') &&
    g'`o`f == f'`o`g

hPushout_g :: CoSpan Morphism -> CoSpan Morphism -> Morphism
hPushout_g pushout@(f' @(Mor _ _ nmf' emf'), g' @(Mor _ _ nmg' emg'))
           other@(f''@(Mor _ _ nmf'' emf''), g''@(Mor _ _ nmg'' emg''))
  | src f' /= src f'' || src g' /= src g'' =
      error "hPushout: some src mismatch"
  | tgt f' /= tgt g' =
      error "hPushout: invalid pushout cospan"
  | tgt f'' /= tgt g'' =
      error "hPushout: invalid secondary cospan"
  | otherwise =
      Mor (tgt f') (tgt f'') nm em where
          nm = map (\n' -> if n'`elem`nmf'
                           then nmf''.>(nmf'<.n')
                           else nmg''.>(nmg'<.n')) (nodesof (tgt f'))
          em = map (\e' -> if e'`elem`emf'
                           then emf''.>(emf'<.e')
                           else emg''.>(emg'<.e')) (edgesof (tgt f'))

hPullback_g :: Span Morphism -> Span Morphism -> Morphism
hPullback_g other@(f' @(Mor src' _ nmf' emf'),  g' @(Mor _ _ nmg' emg'))
            pullback@(f''@(Mor src'' _ nmf'' emf''),g''@(Mor _ _ nmg'' emg''))
  | tgt f' /= tgt f'' || tgt g' /= tgt g'' =
      error "hPullback: some tgt mismatch"
  | src f' /= src g' =
      error "hPullback: invalid secondary span"
  | src f'' /= src g'' =
      error "hPullback: invalid pullback span"
  | otherwise =
      Mor (src f') (src f'') nm em where
          nm = pam (nodesof src')
                   (head.
                    uncurry intersect . (((nmf''<.?) . (nmf'.>))
                                    &&& (((nmg''<.?) . (nmg'.>)))))
          em = pam (edgesof src')
                   (head.
                    uncurry intersect . (((emf''<.?) . (emf'.>))
                                    &&& (((emg''<.?) . (emg'.>)))))

-- (TODO: optimized variant for M-morphisms?)
gPullback :: CoSpan Morphism -> Span Morphism
gPullback (f@(Mor srcf tgtf nmapf emapf),
           g@(Mor srcg tgtg nmapg emapg)) =
  let f' = Mor src' srcg nmapf' emapf'
      g' = Mor src' srcf nmapg' emapg'

      gluon_n = [ ((i,j), k)
                | k <- nodesof tgtf
                , i <- nmapf <.? k
                , j <- nmapg <.? k ]

      gluon_e = [ ((ei,ej), ek)
                | ek <- edgesof tgtf
                , ei <- emapf <.? ek
                , ej <- emapg <.? ek ]

      numnodes_src = lenff gluon_n
      numedges_src = lenff gluon_e
      src' = G numnodes_src
              numedges_src
              (map (\(_,ek) -> nmapf' <. (nmapg <. (ve tgtf .> ek)) ) gluon_e)
              (map (\(_,ek) -> nmapf' <. (nmapg <. (ev tgtf .> ek)) ) gluon_e)

      nmapg' = map ((\((i',_),_) -> i') . (gluon_n .>)) (nodesof src')
      emapg' = map ((\((i',_),_) -> i') . (gluon_e .>)) (edgesof src')
      nmapf' = map ((\((_,j'),_) -> j') . (gluon_n .>)) (nodesof src')
      emapf' = map ((\((_,j'),_) -> j') . (gluon_e .>)) (edgesof src')
  in
    if tgtg /= tgtf
       then error ("pullback: target mismatch, " ++ show f ++ ", " ++ show g)
       else (f', g')

-- Predicate: are the given morphisms jointly surjective?
areJS_g :: CoSpan Morphism -> Bool
areJS_g (Mor _ _ nmf' emf', Mor _ tgt2 nmg' emg') =
    nodesof tgt2 == sortNub (nmf' ++ nmg') &&
    edgesof tgt2 == sortNub (emf' ++ emg')

-- Pushout complement with injective 1st argument
-- Format: forward in, forward out.
pocM_g :: Morphism -> Morphism -> [(Morphism,Morphism)]
pocM_g f @(Mor srcf  tgtf  nmapf  emapf)
       g'@(Mor srcg' tgtg' nmapg' emapg')
  | tgtf /= srcg'   = error "pocM: source/target mismatch"
  | not (isMono  f) = error "pocM of non-Mono"
  | otherwise =
      let n_added_tgt     = filter (`notElem`nmapg') (nodesof tgtg')
          n_from_tgtf_src = filter (`elem` composeIRel nmapf nmapg') (nodesof tgtg')
          n_added_tgtf    = map (nmapg'.>) (filter (`notElem`nmapf) (nodesof tgtf))
          e_added_tgt     = filter (`notElem`emapg') (edgesof tgtg')
          e_from_tgtf_src = filter (`elem` composeIRel emapf emapg') (edgesof tgtg')
          criterion  =  all ((\(s,t) -> s`notElem`n_added_tgtf &&
                                        t`notElem`n_added_tgtf) .
                             (srctgt tgtg')) e_added_tgt
                     && all (\i -> lenff (fiff (==(nmapg' .> i)) nmapg') == 1)
                        (filter (`notElem`nmapf) (nodesof tgtf))
                     && all (\i -> lenff (fiff (==(emapg' .> i)) emapg') == 1)
                        (filter (`notElem`emapf) (edgesof tgtf))

          -- first, the images via f of all nodes in src,
          -- glued according to g' and renumbered,
          -- then the new nodes, renumbered with offset
          nmapg      = map ((n_from_tgtf_src <.).(nmapg'.>).(nmapf.>)) (nodesof srcf)
          emapg      = map ((e_from_tgtf_src <.).(emapg'.>).(emapf.>)) (edgesof srcf)
          nmapf'     = n_from_tgtf_src
                       ++ n_added_tgt
          emapf'     = e_from_tgtf_src
                       ++ e_added_tgt
          veevtgtg   = \veev -> 
                         pam (e_from_tgtf_src ++ e_added_tgt) (\i -> (nmapf'<.) (veev tgtg' .> i) )
          tgtg = G (v tgtg' - lenff (filter (`notElem`nmapf) (nodesof tgtf)))
                   (e tgtg' - lenff (filter (`notElem`emapf) (edgesof tgtf)))
                   (veevtgtg ve) (veevtgtg ev)
      in
        [ (Mor srcf tgtg nmapg emapg, Mor tgtg tgtg' nmapf' emapf') | criterion ]
      
-- (TODO: more efficient pushout code for M-morphisms.)
-- Some functions could be written more succinctly if items (nodes, edges) could be handled generically.

-- (f,g) -> (f',g') such that f'g = g'f pushout
gPushout :: Span Morphism -> CoSpan Morphism
gPushout (f@(Mor srcf tgtf nmapf emapf),
          g@(Mor srcg tgtg nmapg emapg)) =
  let
      n_added_f = filter (`notElem`nmapf) (nodesof tgtf)
      e_added_f = filter (`notElem`emapf) (edgesof tgtf)
      n_added_g = filter (`notElem`nmapg) (nodesof tgtg)
      e_added_g = filter (`notElem`emapg) (edgesof tgtg)

      -- Construct auxiliary graph to determine gluing components, (itemsort)-component-wise.
      gluon sel mapf mapg =
          let conngraph = G (sel srcf + sel tgtf + sel tgtg)
                            (sel srcf + sel srcf)
                            ([0..sel srcf-1] ++ [0..sel srcf-1])
                            ([sel srcf + it'| it'<- mapf] ++ [sel srcf + sel tgtf + it'| it'<- mapg])
                          in
          -- traceShow conngraph $
          filter (not . S.null) $
                      map (S.filter (<sel srcf)) (cc conngraph)

      gluon_n = gluon v nmapf nmapg
      gluon_e = gluon e emapf emapg

      -- Determine where in D the common items of srcf are mapped:
      common_gluemap_n :: [Integer] = map (\nid -> findfirst (nid ∈) gluon_n) (nodesof srcf)
      common_gluemap_e :: [Integer] = map (\eid -> findfirst (eid ∈) gluon_e) (edgesof srcf)

      -- Numbering: possibly glued common, then added f, added g (ve respecting gluing)
      d  = G (lenff gluon_n + lenff n_added_f + lenff n_added_g)
             (lenff gluon_e + lenff e_added_f + lenff e_added_g)
             (dveev ve) (dveev ev)

      dveev = \veev ->
              [(common_gluemap_n .>) (veev srcf .> S.findMin es) | es <- gluon_e] ++
              map ((nmapg' .>) . (veev tgtf  .>)) e_added_f ++
              map ((nmapf' .>) . (veev tgtg  .>)) e_added_g

      mapconstruct :: (Eq a) => [a] -> [a] -> Integer -> [Integer] -> [a] -> [Integer]
      mapconstruct = \baseset addeds offset commongluemap itemmap_1stmorphism ->
        pam baseset (\it -> case fiff (==it) addeds of
                              (h:_) -> h + offset
                              []    -> commongluemap .> (itemmap_1stmorphism <. it))

      nmapg' = mapconstruct (nodesof tgtf) n_added_f (lenff gluon_n) common_gluemap_n nmapf
      emapg' = mapconstruct (edgesof tgtf) e_added_f (lenff gluon_e) common_gluemap_e emapf
      nmapf' = mapconstruct (nodesof tgtg) n_added_g (lenff (nub nmapg')) common_gluemap_n nmapg
      emapf' = mapconstruct (edgesof tgtg) e_added_g (lenff (nub emapg')) common_gluemap_e emapg

      f' = Mor tgtg d nmapf' emapf'
      g' = Mor tgtf d nmapg' emapg'   
  in
    if srcf /= srcg
       then error (printf "pushout: source mismatch %s %s" (show srcf) (show srcg))
       else (f', g')
