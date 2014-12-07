{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Tree where

import Prelude hiding (reverse)
import Data.FAlgebra.Base
import Data.FAlgebra.Annotation
import Data.Proxy

data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord)

instance Functor (TreeF a) where
    fmap _ Empty = Empty
    fmap f (Branch a b1 b2) = Branch a (f b1) (f b2)

type Tree a = Fix (TreeF a)

branch :: FAlgebra (TreeF a) t => a -> t -> t -> t
branch a b1 b2 = alg $ Branch a b1 b2

leaf :: forall a t. FAlgebra (TreeF a) t => a -> t
leaf a = branch a e e
    where
    e = alg (Empty :: TreeF a t)

empty :: forall a t. FAlgebra (TreeF a) t => t
empty = alg (Empty :: TreeF a t)

left :: forall a t. FCoalgebra (TreeF a) t => t -> t
left t = case (coalg t :: TreeF a t) of
    Empty -> t
    Branch _ l _ -> l

right :: forall a t. FCoalgebra (TreeF a) t => t -> t
right t = case (coalg t :: TreeF a t) of
    Empty -> t
    Branch _ _ r -> r

newtype Size = Size Int deriving (Eq, Show, Ord, Num)

instance FAlgebra (TreeF a) Size where
    alg Empty = 0
    alg (Branch _ b1 b2) = 1 + b1 + b2

type SizeTreeF a = AnnF Size (TreeF a)

type SizeTree a = Fix (SizeTreeF a)

getSize :: Structured (AnnM Size) a => a -> Size
getSize = getAnnotation

newtype Sum a = Sum a deriving (Eq, Show, Ord, Num)

instance Num a => FAlgebra (TreeF a) (Sum a) where
    alg Empty = 0
    alg (Branch a b1 b2) = Sum a + b1 + b2

type SumTreeF a = AnnF (Sum a) (TreeF a)
type SumTree a = Fix (SumTreeF a)

type SumAndSizeTreeF a = AnnF Size (AnnF (Sum a) (TreeF a))
type SumAndSizeTree a = Fix (SumAndSizeTreeF a)

getSum :: Structured (AnnM (Sum a)) t => t -> Sum a
getSum = getAnnotation

getAnnotation :: Structured (AnnM a) t => t -> a
getAnnotation = runAnnM struct 

-- These instances that are maximally general on f serve as a sort of
-- alternative to functional dependencies, so you can, for example,
-- write coalg t without explicit type signatures.
instance (f ~ TreeF a) => FAlgebra f (Tree a) where
    alg = algNat

instance (f ~ TreeF a) => FCoalgebra f (Tree a) where
    coalg = coalgNat

instance (f ~ TreeF a) => FAlgebra f (SizeTree a) where
    alg = algRNat (Proxy :: Proxy (AnnM Size))

instance (f ~ TreeF a) => FCoalgebra f (SizeTree a) where
    coalg = coalgNat

instance (f ~ TreeF a, Num a) => FAlgebra f (SumTree a) where
    alg = algRNat (Proxy :: Proxy (AnnM (Sum a)))

instance (f ~ TreeF a, Num a) => FCoalgebra f (SumTree a) where
    coalg = coalgNat

instance (f ~ TreeF a, Num a) => FAlgebra f (SumAndSizeTree a) where
    alg = algRNat (Proxy :: Proxy (AnnM (Sum a) :*: AnnM Size))

instance (f ~ TreeF a, Num a) => FCoalgebra f (SumAndSizeTree a) where
    coalg = coalgNat

data RevF f a = RevF !Bool (f a) deriving (Eq, Show, Ord, Functor)

revSnd :: RevF f a -> f a
revSnd ~(RevF _ as) = as

newtype RevM a = RevM { runRevM :: a -> a }

reverse :: Structured RevM a => a -> a
reverse = runRevM struct

-- TODO: Can this be automated?
instance IsoRespecting RevM where
    liftIso (Iso to from) = Iso revTo revFrom
        where
        revTo (RevM r) = RevM (to . r . from)
        revFrom (RevM r) = RevM (from . r . to)

instance Preserving RevM (TreeF a) where
    trans (RevM r) = RevM $ \t -> case t of
        Empty -> Empty
        Branch a b1 b2 -> Branch a (r b2) (r b1)

instance (Structured RevM a, Preserving RevM f) => Preserving RevM (AnnF a f) where
    trans rev = RevM $ \(AnnF a xs) ->
        AnnF (reverse a) (runRevM (trans rev) xs)

instance Structured RevM (RevF f a) where
    struct = RevM $ \(RevF r xs) -> RevF (not r) xs

-- RevF "captures" the reverse operation
instance Preserving RevM (RevF f) where
    trans (RevM _) = RevM reverse

instance (f ~ f') => Natural f (RevF f') where
    nat = RevF False

-- Coalgebra instance is
-- Fix (RevF f) -> RevF (f (Fix (RevF f))) -> f (Fix (RevF f))
-- TODO: Can RevM go outside of annotations?
-- For size & sum annotations, reversing does not change their value.
instance Structured RevM Size where
    struct = RevM id

instance Structured RevM (Sum a) where
    struct = RevM id

type RevTreeF a = RevF (TreeF a)
type RevTree a = Fix (RevTreeF a)

type RevSizeTreeF a = AnnF Size (RevF (TreeF a))
type RevSizeTree a = Fix (RevSizeTreeF a)

instance (f ~ TreeF a) => FAlgebra f (RevTree a) where
    alg = algNat

instance (f ~ TreeF a) => FCoalgebra f (RevTree a) where
    coalg = coalgRNat (Proxy :: Proxy RevM)

instance RestrictedNatural s f f' => RestrictedNatural s f (RevF f') where
    rnat s = RevF False . rnat s

instance (f ~ f', Preserving RevM f) => RestrictedConatural RevM f (RevF f') where
    rconat _ (RevF False as) = as
    rconat rev (RevF True as) = runRevM (trans rev) as

instance (f ~ TreeF a) => FAlgebra f (RevSizeTree a) where
    alg = algRNat (Proxy :: Proxy (AnnM Size))

instance (f ~ TreeF a) => FCoalgebra f (RevSizeTree a) where
    coalg = coalgRNat (Proxy :: Proxy RevM)
