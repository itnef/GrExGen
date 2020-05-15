{-# LANGUAGE ScopedTypeVariables, FunctionalDependencies #-}

{- Generic definitions for (M-)adhesive categories. -}

module Category.Category where

class Category g m | m -> g where
    idmor :: g -> m
    o  :: m -> m -> m
    srcm :: m -> g
    tgtm :: m -> g

-- Type system: cannot specify the context Category o m. I'm sure there's a good reason for that.
type Span m   = (m, m)
type CoSpan m = (m, m)
type FwdComposablePair m = (m, m)

-- Useful queries:
class (Category g m) => CatExtra g m | m -> g where
    isIdmor :: m -> Bool
    isMono :: m -> Bool
    isIso :: m -> Bool
    isEq  :: m -> Bool
    areJS :: CoSpan m -> Bool
    -- Applicable only to Isos:
    inv :: m -> m
    -- Given f g, does f`o`g exist?
    composable :: m -> m -> Bool
