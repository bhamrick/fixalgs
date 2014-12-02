{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- For testing code
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

-- Testing it out
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
