{-# LANGUAGE FunctionalDependencies, RankNTypes #-}

{- Generic constructions for (M-)adhesive categories.
 - (see Lack, Sobociński, 2004: "Adhesive Categories", FOSSACS'04, LNCS 2987)
 -}

module Category.Adhesive where

import Category.Category
import Graph

class (Category o m) => Adhesive o m | m -> o where
    initial  :: o -> m
    pullback :: CoSpan m -> Span m
    pushout  :: Span m -> CoSpan m
    hPushout :: CoSpan m -> CoSpan m -> m -- from PO to some
    hPullback :: Span m -> Span m -> m    -- from some to PB
    -- kludge:
    ø :: m -> o -- it has to be (Adhesive.ø øhelper)
    øhelper :: m
    øhelper = error "" -- no, GHC, there's nothing "ambiguous" about the type here
    -- the empty set sign btw is a syntax error: this is Danish ø, which is fine.
    -- input: forward in; forward out:
    pocM  ::  m -> m -> [FwdComposablePair m]

-- Swiss army knife of DPO graph rewriting theory
makeJointlySurjective :: forall o m. (Adhesive o m) => CoSpan m -> CoSpan m
makeJointlySurjective = pushout . pullback
makeJS :: (Adhesive o m) => CoSpan m -> CoSpan m
makeJS = makeJointlySurjective

-- Factor out a common postcomposed morphism from a list of arrows of same target
multiMakeJS :: (Adhesive o m, Show m) => [m] -> (Maybe m, [m])
multiMakeJS []     = (Nothing, [])
multiMakeJS [h]    = (Just (idmor (tgtm h)), [h])
multiMakeJS [i,i2] =
  let (i',i2') = makeJointlySurjective (i,i2)
      h        = hPushout (i',i2') (i,i2)
  in
    (Just h, [i',i2'])
multiMakeJS (ho:t) =
  let rest@(Just h, ms) = multiMakeJS t
      onemore@(Just h', [hoi',hi']) = multiMakeJS [ho, h]
  in
    (Just h', hoi' : map (hi'`o`) ms)

pocMsof :: Adhesive o t => (t, t) -> [(t, t, t, t)]
pocMsof (f,g') = [ (f,g,f',g') | (g,f') <- pocM f g' ]

haspocM :: Adhesive o m => (m, m) -> Bool
haspocM (f,g') = not (null (pocM f g'))

pushoutall :: (Adhesive o m) => [m] -> m
pushoutall [h] = h
pushoutall (h:h2:t) =
  let (_,i) = pushout (h,h2)
  in
    pushoutall (i `o` h:t)
