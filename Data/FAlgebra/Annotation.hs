{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Annotation where

import Data.FAlgebra.Base

-- Isomorphic to CofreeF
data AnnF a f r = AnnF a (f r)
    deriving (Eq, Show)

instance Functor f => Functor (AnnF a f) where
    fmap f (AnnF a as) = AnnF a (fmap f as)

annFst ~(AnnF a _) = a
annSnd ~(AnnF _ as) = as

-- Requires UndecidableInstances due to failing Coverage Condition
instance (Functor f, Functor f', FAlgebra f a, FAlgebraTrans f f') => FAlgebraTrans f (AnnF a f') where
    algf anns = AnnF (alg $ fmap annFst anns) (algf $ fmap annSnd anns)

instance (Functor f, Functor f', FAlgebra f a, FAlgebraTrans f f') => FAlgebraFixable f (AnnF a f') where
    algfix = algfixDefault

-- The "forgetful" f-coalgebra instances doesn't arise as a
-- coalgebra transformer, but we can transform FCoalgebraFixables.

{-
instance (Functor f, FCoalgebraFixable f g) => FCoalgebraFixable f (AnnF a g) where
    -- Want AnnF a g r -> f (AnnF a g r)
    -- via AnnF a g r -> g r -> f (g r) -> f r -> f (AnnF a g r)
    -- fix :: AnnF a g r -> r
    -- unfix :: r -> AnnF a g r
    -- coalgfix :: FAlgebra f r => (r -> g r) -> g r -> f (g r)
    -- annSnd . unfix :: r -> AnnF a g r -> g r
    -- g r -> r
    coalgfix unfix = _ . coalgfix (annSnd . unfix) . annSnd
-}
-- TODO: Is there a way to make a generic "forgetful" f-coalgebra instance?
-- Ideally it should work with nested annotations
-- Prolem is that in the forgetful instance for Fix g, we do
-- Fix g -> g (Fix g) -> f (Fix g)
-- Where the g (Fix g) -> f (Fix g) step is from the fact
-- that g "contains" f, and does not (obviously) factor into
-- g (Fix g) -> f (g (Fix g)) -> f (Fix g)

-- We want the instance for Fix (AnnF a f) to be
-- coalg (Fix (AnnF _ as)) = as

-- i.e.
-- coalg = annSnd . unFix = fmap Fix . coalgf . unFix
-- annSnd = fmap Fix . coalgf
-- fmap unFix . annSnd = coalgf
-- annSnd :: AnnF a f r -> f r
-- unFix :: Fix g -> g (Fix g)

-- Unify:
-- annSnd :: AnnF a f (Fix g) -> f (Fix g)
-- fmap unFix . annSnd :: AnnF a f (Fix g) -> f (g (Fix g))

-- So if we want to replace unFix by coalg, it needs to be a g-coalgebra.

-- Should use the fact that we have a natural transformation
-- AnnF a f -> f given by annSnd
