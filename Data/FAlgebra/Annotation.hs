{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances #-}
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

-- This isn't the proper instance, since it recomputes the annotations that it
-- uses for creating the topmost annotation
-- TODO: What is the proper instance at the finite level?
instance (Functor f, Functor f', FAlgebra f a, Preserving (FAlgebraM f) f') => Preserving (FAlgebraM f) (AnnF a f') where
    trans alg0 = FAlgebraM $ \anns ->
        AnnF (alg $ fmap annFst anns) (runFAlgebraM (trans alg0) $ fmap annSnd anns)

-- Real instance for Fix (AnnF a f) should be
-- f Fix (AnnF a f) -> f (AnnF a f (Fix (AnnF a f))) ->
-- AnnF a f (AnnF a f (Fix (AnnF a f))) ->
-- AnnF a f (Fix (AnnF a f)) -> Fix (AnnF a f)
-- TODO: How to extend this to more than one annotation?
-- Maybe f (AnnF a b) -> f' c -> AnnF a f' c
-- Perhaps this can be encoded as a "Restricted Natural Transformation"
-- Where the structure is s c ~ (c -> a)
-- That extracts the annotation

-- Annotation extracting structure
newtype AnnM a c = AnnM { runAnnM :: c -> a }

instance IsoRespecting (AnnM a) where
    liftIso (Iso to from) = Iso annTo annFrom
        where
        annTo (AnnM getter) = AnnM (getter . from)
        annFrom (AnnM getter) = AnnM (getter . to)

instance Preserving (AnnM a) (AnnF a f) where
    trans _ = AnnM annFst

instance Preserving (AnnM b) f => Preserving (AnnM b) (AnnF a f) where
    trans getB = AnnM (runAnnM (trans getB) . annSnd)

instance (Functor f, RestrictedNatural s f f', FAlgebra f a, s' ~ (s :*: AnnM a)) => RestrictedNatural s' f (AnnF a f') where
    -- f b -> f' b -> AnnF a f' b
    -- Where the annotation comes from the algebra
    -- f b -> f a -> a
    -- and b -> a is from the AnnM structure
    rnat (s :*: (AnnM getAnn)) bs = AnnF (alg (fmap getAnn bs)) . rnat s $ bs

{-
instance (Functor f, FAlgebra f a, s ~ AnnM a) => RestrictedNatural s f (AnnF a f) where
    rnat = undefined
-}

-- GHC wants UndecidableInstances here, but I'm not sure exactly why.
instance RestrictedConatural s f f' => RestrictedConatural s f (AnnF a f') where
    rconat s = rconat s . annSnd

instance Conatural f f' => Conatural f (AnnF a f') where
    conat = conat . annSnd
