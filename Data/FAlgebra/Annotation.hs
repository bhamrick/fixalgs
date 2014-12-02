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
    algfix = algfixTrans

-- The "forgetful" f-coalgebra instances doesn't arise as a
-- coalgebra transformer, but we can transform FCoalgebraNaturals

instance (Functor f, FCoalgebraNatural f f') => FCoalgebraNatural f (AnnF a f') where
    conat = conat . annSnd

instance (Functor f, FCoalgebraNatural f f') => FCoalgebraFixable f (AnnF a f') where
    coalgfix = coalgfixNat
