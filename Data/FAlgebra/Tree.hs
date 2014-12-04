{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Tree where

import Prelude hiding (reverse)
import Data.FAlgebra.Base
import Data.FAlgebra.Annotation

data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord)

instance Functor (TreeF a) where
    fmap f Empty = Empty
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

newtype Sum a = Sum a deriving (Eq, Show, Ord, Num)

instance Num a => FAlgebra (TreeF a) (Sum a) where
    alg Empty = 0
    alg (Branch a b1 b2) = Sum a + b1 + b2

type SumTreeF a = AnnF (Sum a) (TreeF a)
type SumTree a = Fix (SumTreeF a)

type SumAndSizeTreeF a = AnnF Size (AnnF (Sum a) (TreeF a))
type SumAndSizeTree a = Fix (SumAndSizeTreeF a)

-- These instances that are maximally general on f serve as a sort of
-- alternative to functional dependencies, since any other FAlgebra instance
-- would overlap.
instance (f ~ TreeF a) => FAlgebra f (Tree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a) => FCoalgebra f (Tree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM

instance (f ~ TreeF a) => FAlgebra f (SizeTree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a) => FCoalgebra f (SizeTree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM

instance (f ~ TreeF a, Num a) => FAlgebra f (SumTree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a, Num a) => FCoalgebra f (SumTree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM

instance (f ~ TreeF a, Num a) => FAlgebra f (SumAndSizeTree a) where
    algM = Iso runTransFix TransFix <$$> algM

instance (f ~ TreeF a, Num a) => FCoalgebra f (SumAndSizeTree a) where
    coalgM = Iso runNatFix NatFix <$$> coalgM

-- TODO: Make reversibility work!
data ReversibleF f a = ReversibleF Bool (f a) deriving (Eq, Show, Ord, Functor)

class ReversibleFunctor f where
    freverse :: forall a. ReversibleClass a => f a -> f a

class ReversibleClass a where
    reverse :: a -> a

instance (ReversibleFunctor f, ReversibleClass a) => ReversibleClass (f a) where
    reverse = freverse

instance ReversibleFunctor (TreeF a) where
    freverse Empty = Empty
    freverse (Branch a b1 b2) = Branch a (reverse b1) (reverse b2)

instance ReversibleFunctor (ReversibleF f) where
    freverse ~(ReversibleF r x) = ReversibleF (not r) x

instance ReversibleFunctor f => ReversibleClass (Fix f) where
    reverse = Fix . freverse . unFix

revSnd :: ReversibleF f a -> f a
revSnd ~(ReversibleF _ as) = as

{-
What does it look like for ReversibleF (AnnF a (TreeF b))?
(Could probably layer them the other way, but it feels like we should be able to get instances both ways)

TreeF b (ReversibleF (AnnF a (TreeF b)) r) -> ReversibleF (AnnF a (TreeF b)) r

TreeF b (AnnF a (ReversibleF (TreeF b)) r) -> AnnF a (ReversibleF (TreeF b)) r
-}

{-
-- TODO: On hold until generalized fixable is written.
-- TODO: Relax equality constraint to generalize
instance (Functor f, FAlgebraFixable f f', f ~ f') => FAlgebraFixable f (ReversibleF f') where
    algfix fix = ReversibleF False . fmap fix

instance (FCoalgebraNatural f f', ReversibleFunctor f) => FCoalgebraNatural f (ReversibleF f') where
    -- conat :: f' r -> f r
    -- Want to define ReversibleF f' r -> f r
    conat (ReversibleF False as) = conat as
    conat (ReversibleF True as) = reverse (conat as)

instance (FCoalgebraNatural f f', ReversibleFunctor f) => FCoalgebraFixable f (ReversibleF f') where
    coalgfix = coalgfixNat
-}

{-
This is kind of okay but does too much work because it coalgs
the next layer down, which means we don't get to use
reverse . reverse == id
Will easily get operations that modify the entire tree.

instance (t ~ TreeF a, FCoalgebraTrans t f') => FCoalgebraTrans t (ReversibleF f') where
    coalgf (ReversibleF False as) = fmap (ReversibleF False) (coalgf as)
    coalgf (ReversibleF True as) = case coalgf as of
        Empty -> Empty
        Branch a b1 b2 -> Branch a (ReversibleF True b2) (ReversibleF True b1)

instance (t ~ TreeF a, FCoalgebraTrans t f') => FCoalgebraFixable t (ReversibleF f') where
    coalgfix = coalgfixTrans
-}

type ReversibleTreeF a = ReversibleF (TreeF a)
type ReversibleTree a = Fix (ReversibleTreeF a)
