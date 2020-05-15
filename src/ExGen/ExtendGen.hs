{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, TupleSections #-}

{- Example generator and experimentation toolkit for the
   M-adhesive category of finite, unlabeled (MultiDi)Graphs.

   Copyleft 2014-16(?) Nils Erik Flick
   flick at informatik.uni-oldenburg.de
   ( PGP: 0xF82D66B403A3E1E5 )
   License: GPL v3
-}

{- Example generator for many different diagrams in the category of Unlabeled Graphs.
 - Can be used for randomised testing of computations in the DPO graph rewriting context,
   to generate examples and counterexamples for teaching, ... -}

-- Missing: generator for random morphisms from a fixed homset.

module ExGen.ExtendGen where

import Sane
import Util
    
import Graph
import GraphOps
import Category.Category as Category
import Category.Adhesive

import Instances.GraphAdhesive

import Data.List (sort, nub, sortBy, groupBy, partition)
    
import Control.Monad
import Control.Arrow
import Control.Applicative ((<$>))

import Data.Function

import Test.QuickCheck

-- Generate arbitrary well-formed graphs.
instance Arbitrary Graph where
  arbitrary = do
      v <- arbitrary`suchThat` (>=0)
      e <- arbitrary`suchThat` (\e -> e>=0 && not (v==0 && e>0))
      ve <- vectorOf (fromIntegral e) (elements [0..v-1])
      ev <- vectorOf (fromIntegral e) (elements [0..v-1])
      return $ G v e ve ev

-- Generate arbitrary well-formed morphisms.
instance Arbitrary Morphism where
   arbitrary = arbitraryMorphismFrom arbitrary

instance {-# OVERLAPPING #-} Arbitrary (CoSpan Morphism) where
    arbitrary = arbitraryCospanTo arbitrary

arbitraryBipartition :: (CoArbitrary a) => Gen[a] -> Gen([a],[a])
arbitraryBipartition gens =
  liftM2 partition arbitrary gens >>= \(z,u) -> return (z,u)

-- Precondition: a must be finite and non empty.
arbitraryNonEmptyPartition :: Gen [a] -> Gen [[a]]
arbitraryNonEmptyPartition gens = do
  l <- fmap length gens
  if l == 0 then fmap (:[]) gens else do
   n <- elements [1..l]
   fmap (map (map snd) . groupBy ((==)`on`fst) . sortBy (compare`on`fst)) (liftM2 zip (vectorOf l (elements [0..n-1])) gens)

arbitraryEpi :: Gen Morphism
arbitraryEpi = arbitraryEpiFrom arbitrary

arbitraryIso :: Gen Morphism
arbitraryIso = arbitraryIsoFrom arbitrary

arbitraryIncl :: Gen Morphism
arbitraryIncl = arbitraryInclFrom arbitrary

arbitraryMono :: Gen Morphism
arbitraryMono = arbitraryMonoFrom arbitrary

arbitraryMonoTo :: Gen Graph -> Gen Morphism
arbitraryMonoTo g = do
  y <- arbitraryIsoTo g
  x <- arbitraryInclTo (only (src y))
  return (y`o`x)

arbitraryMonoFrom :: Gen Graph -> Gen Morphism
arbitraryMonoFrom g = do
  x <- arbitraryInclFrom g
  y <- arbitraryIsoFrom  (only (tgt x))
  return (y`o`x)

only :: x -> Gen x
only = elements . (:[])

arbitraryEpiTo :: Gen Graph -> Gen Morphism
arbitraryEpiTo gg = do
  h@(G vh eh veh evh) <- gg
  let preimages_calc itemsof = concat <$> sequence [ fmap (\num -> map (\i -> (it,i::Integer)) [0..num-1]) (arbitrary`suchThat`(>0)) | it <- itemsof h ]
  v_preimages <- preimages_calc nodesof
  e_preimages <- preimages_calc edgesof
  let nm    = map (\(n,i) -> n) v_preimages
      em    = map (\(e,i) -> e) e_preimages
      npzip = zip v_preimages [0..]
  let incidence_calc veevh = sequence [ elements ( map snd ( filter (\((n,i),idx) -> n == (veevh .> e)) npzip ) ) | (e,_) <- e_preimages ]
  veg <- incidence_calc veh
  evg <- incidence_calc evh
  let g = G (lenff v_preimages) (lenff e_preimages) veg evg
  return (Mor g h nm em)

-- Select an arbitrary isomorphism starting from a graph arbitrarily chosen from input.
arbitraryEpiFrom :: Gen Graph -> Gen Morphism
arbitraryEpiFrom gg = do
  g <- gg
  
  -- first, choose how to glue the nodes.
  nodeglueraw <- vectorOf (fromIntegral (v g)) (arbitrary `suchThat` (>=0)) :: Gen [Integer]
  
  -- "rectify" the random indices to [0..new #vertices]:
  let rectids' = nub nodeglueraw
  let nmap     = map (`firstindex`rectids') nodeglueraw :: [Integer]
  
  -- if two edges are parallel in the nodeglued graph, then we can put them into an equivalence class.
  let edgeglueable =
          groupSortBy (\e -> nmap`atff2`srctgt g e) [0..e g-1]

  -- glue them. no pair of edges /have/ to be merged except by transitivity.
  edgeglue' <- if e g == 0
               then return []
               else mapM (arbitraryNonEmptyPartition . only) edgeglueable

  let emap = map snd $
             sortBy (compare`on`fst) $
             concatMap (\(i,ls) -> map (,i) ls) $
             zip [0..] (concat edgeglue')
      nume = lenff (concat edgeglue')
      numv = lenff rectids'

  let incidence_h veev = map ((nmap .>) . (veev g .>) . (`firstindex`emap)) [0..nume-1]
      h = G numv nume (incidence_h ve) (incidence_h ev)

  return (Mor g h nmap emap)

arbitraryInclTo :: Gen Graph -> Gen Morphism
arbitraryInclTo gg = do
  g@(G vg _ veg evg) <- gg
  vorder <- arbitraryPermutation (only (nodesof g))
  v'     <- arbitrary `suchThat` (\z -> z <= vg && z >= 0)
  
  let vmap = sort (takeff v' vorder)
  let ok_edges = filter
                   (\e -> (veg .> e)`elem`vmap && (evg .> e)`elem`vmap)
                   (edgesof g)
  eorder <- arbitraryPermutation (only ok_edges)
  e'     <- arbitrary `suchThat` (\z -> z <= lenff eorder && z >= 0)
  
  let emap = sort (takeff e' eorder)
      veev' = \veevg -> map ((vmap<.).(veevg .>)) emap
      (ve',ev') = two veev' (veg, evg)

  let h = G v' e' ve' ev'
  return (Mor h g vmap emap)

arbitraryInclFrom :: Gen Graph -> Gen Morphism
arbitraryInclFrom gg = do
  g <- gg
  v' <- arbitrary `suchThat` (>= v g)
  e' <- arbitrary `suchThat` (\x -> x >= e g && not (x > 0 && v g == 0))
  let make_incidence = if v' == 0 then return [] else vectorOf (fromIntegral $ e' - e g) (arbitrary `suchThat` (\x -> x<v' && x>=0))
  ve'' <- make_incidence
  ev'' <- make_incidence
  let h = G v' e' (ve g ++ ve'') (ev g ++ ev'')
  return $ Mor g h [0..v g-1] [0..e g-1]

arbitraryPermutation :: Gen [a] -> Gen [a]
arbitraryPermutation gens = do
  l <- fmap length gens
  if l == 0
     then return []
     else do
       x <- elements [0..l-1]
       z <- fmap (take x) gens
       u <- fmap (drop (x+1)) gens
       a <- fmap (!!x) gens
       fmap (mplus [a]) (arbitraryPermutation (only (z++u)))

-- Clearly, taking arbitrary Iso mappings backwards also yields all Isos.
arbitraryIsoTo :: Gen Graph -> Gen Morphism
arbitraryIsoTo gg = do
  iso@(Mor g h nm em) <- arbitraryIsoFrom gg
  return $ Mor h g (inversePerm nm) (inversePerm em)

arbitraryIsoFrom :: Gen Graph -> Gen Morphism
arbitraryIsoFrom gg = do
  g <- gg
  nperm <- arbitraryPermutation (only [0..v g-1])
  eperm <- arbitraryPermutation (only [0..e g-1])
  let (npve,npev) = two (map (nperm .>)) (ve g, ev g)
  let h = G (v g) (e g) (map (npve .>) eperm) (map (npev .>) eperm)
  return $ Mor g h nperm (inversePerm eperm)

-- Correct, but too slow
arbitraryAutomorphism :: Gen Graph -> Gen Morphism
arbitraryAutomorphism gr = do
  g <- gr
  arbitraryIsoFrom (only g) `suchThat` (\i -> srcm i == tgtm i)

arbitraryMorphismTo :: Gen Graph -> Gen Morphism
arbitraryMorphismTo gr = do
  g <- arbitraryEpiTo gr
  f <- arbitraryMonoTo (only (src g))
  return (g`o`f)

arbitraryMorphismFrom :: Gen Graph -> Gen Morphism
arbitraryMorphismFrom gr = do
  f <- arbitraryMonoFrom gr
  g <- arbitraryEpiFrom  (only (tgt f))
  return (g`o`f)

arbitrarySpanFrom :: Gen Graph -> Gen (Span Morphism)
arbitrarySpanFrom gg = do
  gr <- gg
  f <- arbitraryMorphismFrom (only gr)
  g <- arbitraryMorphismFrom (only gr)
  return (f,g)

arbitraryCospanTo :: Gen Graph -> Gen (CoSpan Morphism)
arbitraryCospanTo gg = do
  gr <- gg
  f <- arbitraryMorphismTo (only gr)
  g <- arbitraryMorphismTo (only gr)
  return (f,g)

arbitraryLeftMCospanTo :: Gen Graph -> Gen (CoSpan Morphism)
arbitraryLeftMCospanTo gg = do
  gr <- gg
  f <- arbitraryMonoTo (only gr)
  g <- arbitraryMorphismTo (only gr)
  return (f,g)

arbitraryMCospanTo :: Gen Graph -> Gen (CoSpan Morphism)
arbitraryMCospanTo gg = do
  gr <- gg
  f <- arbitraryMonoTo (only gr)
  g <- arbitraryMonoTo (only gr)
  return (f,g)

arbitraryPushoutSquare :: Gen (Morphism, Morphism, Morphism, Morphism)
arbitraryPushoutSquare = do
  let gg = arbitrary
  (f,g) <- arbitrarySpanFrom gg
  let (f',g') = pushout (f,g)
  return (f, g, f', g')

arbitraryPullbackSquare :: Gen (Morphism, Morphism, Morphism, Morphism)
arbitraryPullbackSquare = do
  let gg = arbitrary
  (f',g') <- arbitraryCospanTo gg
  let (f,g) = pullback (f',g')
  return (f, g, f', g')

arbitraryLeftMPullbackSquare :: Gen (Morphism, Morphism, Morphism, Morphism)
arbitraryLeftMPullbackSquare = do
  let gg = arbitrary
  (f',g') <- arbitraryLeftMCospanTo gg
  let (f,g) = pullback (f',g')
  return (f, g, f', g')

type CommutingSquare = (Morphism, Morphism, Morphism, Morphism)

arbitraryMPullbackSquare :: Gen (Morphism, Morphism, Morphism, Morphism)
arbitraryMPullbackSquare = do
  let gg = arbitrary
  (f',g') <- arbitraryMCospanTo gg
  let (f,g) = pullback (f',g')
  return (f, g, f', g')

genPair :: Gen a -> Gen b -> Gen (a,b)
genPair mm nn = do
  m <- mm
  n <- nn
  return (m,n)

arbitraryFactorization :: Gen Morphism -> Gen (FwdComposablePair Morphism)
arbitraryFactorization mm = do
   m@(Mor src tgt nm em) <- mm
   
   let epre = [ ( e, em <.? e ) | e <- edgesof tgt ]
   em_postpone <-
      map  (second (filter (not.null))) <$>
      mapM (uncurry genPair . ( only *** ( arbitraryNonEmptyPartition . only ))) epre
      
   let withcount stuff fn = map snd . sortBy (compare`on`fst) $
                                snd ( foldr fn (0, []) stuff )
       calc postponelist = map ( \x -> 
                    withcount postponelist
                    ( \(e,pre) (count,accum) ->
                        let contrib = x count e pre 
                        in  ( count + lenff pre, contrib ++ accum )))
       subjects =
           [ \count e pre -> [ (e', i) | (i, e's) <- zip [count..] pre , e' <- e's ]
           , \count e pre -> [ (i, e)  | (i, e's) <- zip [count..] pre ] ]
       [ emh1g , emh2 ] = calc em_postpone subjects
   let x2 = G (v tgt) (sum . map (lenff.snd) $ em_postpone)
              (ve tgt ..> emh2) (ev tgt ..> emh2)
       h2  = Mor x2 tgt (nodesof x2) emh2
       h1g = Mor src x2 (nmap m) emh1g
       
   let npre = [ ( n, nm <.? n ) | n <- nodesof x2 ]
   nm_postpone <-
      map  (second (filter (not.null))) <$>
      mapM ( uncurry genPair . ( only *** ( arbitraryNonEmptyPartition . only ))) npre
      
   let [ nmg, nmh1 ]  = calc nm_postpone subjects
       x1'' = G (sum . map (lenff.snd) $ nm_postpone) (e src)
                (nmg ..> ve src) (nmg ..> ev src)
       g''  = Mor src x1'' nmg  (edgesof src)
       h1'' = Mor x1'' x2  nmh1 emh1g
   x1plusn <- if v x2 > 0 then arbitrary`suchThat`(>=0) else only 0
   
   let newnodes = takeff x1plusn [v x1'' ..]
   assocsn  <- sequence (pam newnodes
                             (\n'' -> do
                               n <- elements (nodesof x2)
                               return (n'',n)) )
   let x1' = disjun x1'' (G x1plusn 0 [] [])
       x1''x1' = embed x1'' x1'
       g'  = x1''x1'`o`g''
       h1' = Mor x1' x2 (nmap h1'' ++ map snd assocsn)
                        (emap h1'')
   
   x1pluse <- if e x2 > 0 then arbitrary`suchThat`(>=0) else only 0
   
   let newedges = takeff x1pluse [e x1' ..]
   assocse  <- sequence (pam newedges
                             (\e' -> do
                               e     <- elements (edgesof x2)
                               nfrom <- elements (nmap h1' <.? (ve x2 .> e))
                               nto   <- elements (nmap h1' <.? (ev x2 .> e))
                               return (e', (e, nfrom, nto))))
   let x1 =  unbroken $ broken x1' +-+
             broken (G 0 x1pluse
                       (map (snd3 . snd) assocse)
                       (map (þrd3 . snd) assocse))
       x1'x1 = embed x1' x1
       g = x1'x1`o`g'
       h1 = Mor x1 x2 (nmap h1') (emap h1' ++ map (fst3 . snd) assocse)
   
   nmi  <- arbitraryPermutation (only (nodesof x1))
   emi' <- arbitraryPermutation (only (edgesof x1))
   let x1' = G (v x1) (e x1) (nmi ..> (ve x1 ..> emi')) (nmi ..> (ev x1 ..> emi'))
   let i = Mor x1 x1' nmi (inversePerm emi')
   return (i `o` g, h2 `o` h1 `o` Category.inv i)
