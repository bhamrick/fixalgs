{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- Testing pragmas
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
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

-- Testing annotations
newtype Size = Size Int
    deriving (Eq, Show, Ord, Num)

instance FAlgebra (TreeF a) Size where
    alg Empty = 0
    alg (Branch _ b1 b2) = 1 + b1 + b2

newtype Sum a = Sum a
    deriving (Eq, Show, Ord, Num)

-- Could extend to monoids
instance Num a => FAlgebra (TreeF a) (Sum a) where
    alg Empty = 0
    alg (Branch a b1 b2) = Sum a + b1 + b2

type SizeTree a = Fix (AnnF Size (TreeF a))
type SumTree a = Fix (AnnF (Sum a) (TreeF a))
type SizeAndSumTree a = Fix (AnnF Size (AnnF (Sum a) (TreeF a)))

-- These instances that are maximally general on f serve as a sort of
-- alternative to functional dependencies, since any other FAlgebra instance
-- would overlap.
instance (f ~ TreeF a) => FAlgebra f (SizeTree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a) => FCoalgebra f (SizeTree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM

instance (f ~ TreeF a, Num a) => FAlgebra f (SumTree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a, Num a) => FCoalgebra f (SumTree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM

instance (f ~ TreeF a, Num a) => FAlgebra f (SizeAndSumTree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a, Num a) => FCoalgebra f (SizeAndSumTree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM
