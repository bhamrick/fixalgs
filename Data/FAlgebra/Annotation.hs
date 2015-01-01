{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE RankNTypes #-}

module Data.FAlgebra.Annotation where

import Prelude hiding (sequence)

import Data.FAlgebra.Base
import Data.Functor
import Data.Traversable

import Lens.Micro

-- Isomorphic to CofreeF
data AnnF a f r = AnnF !a (f r)
    deriving (Eq, Show)

instance Functor f => Functor (AnnF a f) where
    fmap f (AnnF a as) = AnnF a (fmap f as)

annFst ~(AnnF a _) = a
annSnd ~(AnnF _ as) = as

-- Lenses
_ann :: Functor f => LensLike f (AnnF a g r) (AnnF b g r) a b
_ann f ~(AnnF a rs) = flip AnnF rs <$> f a

_dat :: Functor f => LensLike f (AnnF a g r) (AnnF a g' s) (g r) (g' s)
_dat f ~(AnnF a rs) = AnnF a <$> f rs

-- This works, but generally not what you want to do because it recomputes annotations for the previous level
instance (Functor f, Functor f', FAlgebra f a, Preserving (FAlgebraM f) f') => Preserving (FAlgebraM f) (AnnF a f') where
    trans alg0 = FAlgebraM $ \anns ->
        AnnF (alg $ fmap annFst anns) (runFAlgebraM (trans alg0) $ fmap annSnd anns)

-- Annotation extracting structure
newtype AnnM a b = AnnM { runAnnM :: b -> a }

type Annotated a b = Structured (AnnM a) b

getAnnotation :: Annotated a t => t -> a
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
    rnat (s :*: AnnM getAnn) bs = AnnF (alg (fmap getAnn bs)) . rnat s $ bs

instance RestrictedConatural s f f' => RestrictedConatural s f (AnnF a f') where
    rconat s = rconat s . annSnd

instance Conatural f f' => Conatural f (AnnF a f') where
    conat = conat . annSnd

-- Annotating an existing fixed point structure
-- First, purely
annotate :: Functor f => (f a -> a) -> Fix f -> Fix (AnnF a f)
annotate = fmapFix . annotateStep
    where
    -- annotateStep :: (Functor f, Structured (AnnM a) b) => (f a -> a) -> f b -> AnnF a f b
    annotateStep combine bs = AnnF (combine (fmap getAnnotation bs)) bs

-- Annotations inside of a monadic context
annotateM :: (Traversable f, Functor m, Monad m) => (f a -> m a) -> Fix f -> m (Fix (AnnF a f))
annotateM buildAnnStep = sequenceFix semisequence
    where
    -- semisequence :: Structured (AnnM a) b => f (m b) -> m (AnnF a f b)
    semisequence bs = do
        bs' <- sequence bs
        let as = fmap getAnnotation bs'
        ann <- buildAnnStep as
        return $ AnnF ann bs'
