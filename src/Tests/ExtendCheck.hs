{- Randomised test of some properties with QuickCheck. Can be impossibly slow
   if the generated instances are too large, but should not fail for logical reasons. -}

module Tests.ExtendCheck where

import Sane
import Util
    
import Graph
import GraphOps
import Extend
import Instances.GraphAdhesive
import Category.Category (o, isIso, areJS)

import Data.List (intersect)

import Category.Adhesive
import Test.QuickCheck

import Control.Monad (liftM)

import ExGen.ExtendGen

ig :: Integer -> IO Graph
ig size =
  liftM head $ sample' (arbitrary `suchThat` (\(G v e _ _) -> v + e > size))

propvalidmor :: Property
propvalidmor = conjoin [forAll (arbitraryMorphismTo arbitrary) isValidMor,
                        forAll (arbitraryMorphismFrom arbitrary) isValidMor]

propAssociative :: Property
propAssociative = forAll (do
                 z <- arbitraryMorphismFrom arbitrary
                 y <- arbitraryMorphismFrom (elements [tgt z])
                 x <- arbitraryMorphismFrom (elements [tgt y])
                 return (x,y,z))
        (\(x,y,z) -> (x`o`y)`o`z == x`o`(y`o`z))

propValidMorphism :: Property
propValidMorphism = forAll arbitrary isValidMor

propValidMorphisms1a :: Property
propValidMorphisms1a =
  conjoin [forAll arbitraryIso isValidMor,
           forAll arbitraryEpi isValidMor,
           forAll arbitraryMono isValidMor,
           forAll arbitraryIncl isValidMor]

pscc01 :: Property
pscc01 = forAll positive (isStronglyConnected . grcycle)

pscc02 :: Property
pscc02 = forAll positive (not . isStronglyConnected . star . (+2))

positive :: Test.QuickCheck.Gen Integer
positive = arbitrary`suchThat`(>=0)

arbitraryFwdComposablePair = do
  f  <- arbitraryMonoFrom arbitrary
  g' <- arbitraryMorphismFrom (elements [tgt f])
  return (f,g')

-- prop_resultsInValidPushout -- or at least SAME as our pushout construction
prop2M :: Property
prop2M = forAll arbitraryFwdComposablePair
                (\(f,g') -> conjoin [ h`o`g''==g' && h`o`f''==f' && isIso h
                                    | (g,f') <- pocM f g'
                                    , let (f'',g'') = pushout (f,g)
                                    , h <- extends g' g'' /\ extends f' f''
                                    ])

-- pocM must output exactly one or zero elements.
prop3 :: Property
prop3 = forAll arbitraryFwdComposablePair
                (\(f,g') -> lenff (pocM f g') < 2)

-- joint surjectivity
propjs1 = forAll (arbitraryPushoutSquare >>= \(f,g,f',g') -> return (f',g') ) areJS

-- not implemented: GENERAL pushout complements
-- propjs2 = forAll (do f  <- arbitraryMorphismFrom arbitrary
--                      g' <- arbitraryMorphismFrom (elements [tgt f])
--                      let ls = poc_g f g'
--                      return [(f',g') | (g,f') <- ls]) (conjoin . (map areJS))

propjs2M = forAll (do f  <- arbitraryMonoFrom arbitrary
                      g' <- arbitraryMorphismFrom (elements [tgt f])
                      let ls = pocM f g'
                      return [(f',g') | (g,f') <- ls]) (conjoin . map areJS)

sample'' = liftM head . sample'  

-- propXetendsDoesWhatItIsSupposedToDo
-- caution, extremely slow.
propXetendsM = forAll (do
                       g <- arbitraryMono
                       (_,f) <- arbitraryFactorization (only g)
                       let h = xetendsM' g f
                       return (f,g,f`o`h)
                     )
                     (\(f,g,foh) -> foh == g)

propXetends = forAll (do
                       g <- arbitrary
                       
                       (_,f) <- arbitraryFactorization (only g)
                       let z = (g,f)
                       let hs = xetends g f
                       h <- elements hs
                       return (f,g,f`o`h,z)
                     )
                     (\(f,g,foh,z) ->
                        foh == g)

-- At least we can check this ...
propArbFactCorrect = forAll (do
                              f     <- arbitrary
                              (g,h) <- arbitraryFactorization (only f)
                              return (f,(g,h),h`o`g))
                             (\(f,(g,h),f') -> f' == f)

propHPushoutUniqueCorrect =
  forAll
    (do
      m <- arbitrary
      (g,f'') <- arbitraryFactorization (only m)
      (f,g'') <- arbitraryFactorization (only m)
      return (f,g,f'',g'')
    )
    (\(f,g,f'',g'') ->
         let (f',g') = pushout (f,g)
             h = hPushout_g (f',g') (f'',g'')
             xy1 = (extends f'' f')
             xy2 = (extends g'' g')
         in
           traceshow (lenff xy1, lenff xy2) $
           [h] == intersect xy1 xy2 -- slow
    )

-- (TODO "check" for uniqueness.)
propHPushoutCorrect :: Property
propHPushoutCorrect =
  forAll
    (do
      m <- arbitrary
      (g,f'') <- arbitraryFactorization (only m)
      (f,g'') <- arbitraryFactorization (only m)
      return (f,g,f'',g'')
    )
    (\(f,g,f'',g'') ->
         let (f',g') = pushout (f,g)
             h = hPushout_g (f',g') (f'',g'')
         in
           (h`o`f' == f'') && (h`o`g' == g'')
    )

propHPullbackCorrect =
  forAll
    (do
      m <- arbitrary
      (g'',f) <- arbitraryFactorization (only m)
      (f'',g) <- arbitraryFactorization (only m)
      return (f'',g'',f,g)
    )
    (\(f'',g'',f,g) ->
         let (f',g') = gPullback (f,g)
             h = hPullback_g (f'',g'') (f',g')
         in
           (f'`o`h == f'') && (g'`o`h == g'') )

main :: IO ()
main = do
  quickCheck propValidMorphism
  quickCheck propValidMorphisms1a
  quickCheck pscc01
  quickCheck pscc02
  -- quickCheck prop2M
  -- quickCheck prop3
  -- quickCheck propjs1
  quickCheck propAssociative
  quickCheck (forAll arbitraryPushoutSquare isValidCommutingSquare)
  quickCheck propHPushoutCorrect
  quickCheck propHPullbackCorrect
