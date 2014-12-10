{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances #-}

module Data.FAlgebra.Annotation where

import Data.FAlgebra.Base

-- Isomorphic to CofreeF
data AnnF a f r = AnnF !a (f r)
    deriving (Eq, Show)

instance Functor f => Functor (AnnF a f) where
    fmap f (AnnF a as) = AnnF a (fmap f as)

annFst ~(AnnF a _) = a
annSnd ~(AnnF _ as) = as

-- This isn't the proper instance, since it recomputes the annotations that it
-- uses for creating the topmost annotation
-- TODO: What is the proper instance at the finite level?
instance (Functor f, Functor f', FAlgebra f a, Preserving (FAlgebraM f) f') => Preserving (FAlgebraM f) (AnnF a f') where
    trans alg0 = FAlgebraM $ \anns ->
        AnnF (alg $ fmap annFst anns) (runFAlgebraM (trans alg0) $ fmap annSnd anns)

-- Annotation extracting structure
newtype AnnM a c = AnnM { runAnnM :: c -> a }

getAnnotation :: Structured (AnnM a) t => t -> a
getAnnotation = runAnnM struct 

instance IsoRespecting (AnnM a) where
    liftIso (Iso to from) = Iso annTo annFrom
        where
        annTo (AnnM getter) = AnnM (getter . from)
        annFrom (AnnM getter) = AnnM (getter . to)

instance Preserving (AnnM a) (AnnF a f) where
    trans _ = AnnM annFst

instance Preserving (AnnM b) f => Preserving (AnnM b) (AnnF a f) where
    trans getB = AnnM (runAnnM (trans getB) . annSnd)

-- Base case instance to avoid needing extraneous Us
instance (Functor f, Natural f f', FAlgebra f a) => RestrictedNatural (AnnM a) f (AnnF a f') where
    rnat (AnnM getAnn) bs = AnnF (alg (fmap getAnn bs)) . nat $ bs

instance (Functor f, RestrictedNatural s f f', FAlgebra f a) => RestrictedNatural (s :*: AnnM a) f (AnnF a f') where
    rnat (s :*: (AnnM getAnn)) bs = AnnF (alg (fmap getAnn bs)) . rnat s $ bs

instance RestrictedConatural s f f' => RestrictedConatural s f (AnnF a f') where
    rconat s = rconat s . annSnd

instance Conatural f f' => Conatural f (AnnF a f') where
    conat = conat . annSnd
