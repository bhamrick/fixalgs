{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Tree where

import Data.FAlgebra.Base
import Data.FAlgebra.Annotation

data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord)

instance Functor (TreeF a) where
    fmap f Empty = Empty
    fmap f (Branch a b1 b2) = Branch a (f b1) (f b2)

type Tree a = Fix (TreeF a)

branch :: FAlgebra (TreeF a) t => a -> t -> t -> t
branch a b1 b2 = alg $ Branch a b1 b2

leaf :: FAlgebra (TreeF a) t => a -> t
leaf a = branch a empty empty

empty :: FAlgebra (TreeF a) t => t
empty = alg Empty

left :: FCoalgebra (TreeF a) t => t -> t
left t = case coalg t of
    Empty -> t
    Branch _ l _ -> l

right :: FCoalgebra (TreeF a) t => t -> t
right t = case coalg t of
    Empty -> t
    Branch _ _ r -> r

newtype Size a = Size Int deriving (Eq, Show, Ord, Num)

instance FAlgebra (TreeF a) (Size a) where
    alg Empty = 0
    alg (Branch _ b1 b2) = 1 + b1 + b2

type SizeTreeF a = AnnF (Size a) (TreeF a)

type SizeTree a = Fix (SizeTreeF a)

newtype Sum a = Sum a deriving (Eq, Show, Ord, Num)

instance Num a => FAlgebra (TreeF a) (Sum a) where
    alg Empty = 0
    alg (Branch a b1 b2) = Sum a + b1 + b2

type SumTreeF a = AnnF (Sum a) (TreeF a)
type SumTree a = Fix (SumTreeF a)

type SumAndSizeTreeF a = AnnF (Size a) (AnnF (Sum a) (TreeF a))
type SumAndSizeTree a = Fix (SumAndSizeTreeF a)

data ReversibleF f a = Reversible Bool (f a) deriving (Eq, Show, Ord, Functor)

reverse :: ReversibleF f a -> ReversibleF f a
reverse ~(Reversible r x) = Reversible (not r) x

revSnd :: ReversibleF f a -> f a
revSnd ~(Reversible _ as) = as

instance (Functor f, FAlgebraTrans f f') => FAlgebraTrans f (ReversibleF f') where
    algf = Reversible False . algf . fmap revSnd

instance (Functor f, FAlgebraTrans f f') => FAlgebraFixable f (ReversibleF f') where
    algfix = algfixTrans
