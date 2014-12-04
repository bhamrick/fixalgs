{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.FAlgebra.Annotation where

import Data.FAlgebra.Base

-- Isomorphic to CofreeF
data AnnF a f r = AnnF a (f r)
    deriving (Eq, Show)

instance Functor f => Functor (AnnF a f) where
    fmap f (AnnF a as) = AnnF a (fmap f as)

annFst ~(AnnF a _) = a
annSnd ~(AnnF _ as) = as

instance (Functor f, Functor f', FAlgebra f a, Preserving (FAlgebraM f) f') => Preserving (FAlgebraM f) (AnnF a f') where
    trans alg0 = FAlgebraM $ \anns ->
        AnnF (alg $ fmap annFst anns) (runFAlgebraM (trans alg0) $ fmap annSnd anns)

instance Conatural f f' => Conatural f (AnnF a f') where
    conat = conat . annSnd
