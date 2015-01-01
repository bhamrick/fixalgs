{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Tree where

import Prelude hiding (reverse)
import Data.FAlgebra.Base
import Data.FAlgebra.Annotation

import Data.Foldable
import Data.Proxy
import Data.Traversable

import Control.Applicative

import Lens.Micro

-- |Functor for trees with values on internal nodes.
data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord)

deriving instance Functor (TreeF a)
deriving instance Foldable (TreeF a)
deriving instance Traversable (TreeF a)

-- |"Lens" for the value of a node. Only works for Applicatives because Empty has no value.
_node :: Applicative f => LensLike f (TreeF a b) (TreeF a' b) a a'
_node _ Empty = pure Empty
_node f (Branch a b1 b2) = fmap (\a' -> Branch a' b1 b2) (f a)

-- |"Lens" For the left branch of a node. Can't change type because left and right need to stay the same type.
_left :: Applicative f => LensLike' f (TreeF a b) b
_left _ Empty = pure Empty
_left f (Branch a b1 b2) = fmap (\b1' -> Branch a b1' b2) (f b1)

-- |"Lens" For the right branch of a node. Can't change type because left and right need to stay the same type.
_right :: Applicative f => LensLike' f (TreeF a b) b
_right _ Empty = pure Empty
_right f (Branch a b1 b2) = fmap (Branch a b1) (f b2)

-- |Sequence root and then both branches
preorder :: Applicative g => TreeF (g a) (g b) -> g (TreeF a b)
preorder Empty = pure Empty
preorder (Branch a b1 b2) = Branch <$> a <*> b1 <*> b2

-- |Sequence the left branch, then the root, then the right branch
inorder :: Applicative g => TreeF (g a) (g b) -> g (TreeF a b)
inorder Empty = pure Empty
inorder (Branch a b1 b2) = (\x y z -> Branch y x z) <$> b1 <*> a <*> b2

-- |Sequence both branches and then the root
postorder :: Applicative g => TreeF (g a) (g b) -> g (TreeF a b)
postorder Empty = pure Empty
postorder (Branch a b1 b2) = (\x y z -> Branch z x y) <$> b1 <*> b2 <*> a

newtype Tree a = Tree { runTree :: Fix (TreeF a) }

deriving instance Show (Fix (TreeF a)) => Show (Tree a)

-- TODO: Reduce boilerplate for newtypes
instance (Functor f, FAlgebra f (Fix (TreeF a))) => FAlgebra f (Tree a) where
    alg = Tree . alg . fmap runTree

instance (Functor f, FCoalgebra f (Fix (TreeF a))) => FCoalgebra f (Tree a) where
    coalg = fmap Tree . coalg . runTree

-- To aid inference (especially in the use of empty)
instance a ~ a' => FAlgebra (TreeF a') (Tree a) where
    alg = Tree . alg . fmap runTree

instance a ~ a' => FCoalgebra (TreeF a') (Tree a) where
    coalg = fmap Tree . coalg . runTree

instance Functor Tree where
    fmap f = Tree . fmapFix (over _node f) . runTree

-- |Create a tree from its children
branch :: FAlgebra (TreeF a) t => a -> t -> t -> t
branch a b1 b2 = alg $ Branch a b1 b2

-- |Create a leaf (a tree with empty children)
leaf :: forall a t. FAlgebra (TreeF a) t => a -> t
leaf a = branch a e e
    where
    e = alg (Empty :: TreeF a t)

-- |Create an empty tree. Using this is a bit tricky due to the ambiguous type.
empty :: forall a t. FAlgebra (TreeF a) t => t
empty = alg (Empty :: TreeF a t)

-- |Get the left branch of a tree
left :: forall a t. FCoalgebra (TreeF a) t => t -> t
left t = case (coalg t :: TreeF a t) of
    Empty -> t
    Branch _ l _ -> l

-- |Get the right branch of a tree
right :: forall a t. FCoalgebra (TreeF a) t => t -> t
right t = case (coalg t :: TreeF a t) of
    Empty -> t
    Branch _ _ r -> r

instance FAlgebra (TreeF a) Size where
    alg Empty = 0
    alg (Branch _ b1 b2) = 1 + b1 + b2

-- The below should probably be moved to Examples/RangeReverse/Main.hs
data RevF f a = RevF !Bool (f a) deriving (Eq, Show, Ord, Functor)

revSnd :: RevF f a -> f a
revSnd ~(RevF _ as) = as

newtype RevM a = RevM { runRevM :: a -> a }

reverse :: Structured RevM a => a -> a
reverse = runRevM struct

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

-- For size annotations, reversing does not change their value.
instance Structured RevM Size where
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

instance (Preserving RevM f', RestrictedConatural RevM f f') => RestrictedConatural RevM f (RevF f') where
    rconat rev (RevF False as) = rconat rev as
    rconat rev (RevF True as) = rconat rev $ runRevM (trans rev) as

instance (f ~ TreeF a) => FAlgebra f (RevSizeTree a) where
    alg = algRNat (Proxy :: Proxy (AnnM Size))

instance (f ~ TreeF a) => FCoalgebra f (RevSizeTree a) where
    coalg = coalgRNat (Proxy :: Proxy RevM)

type SizeRevTreeF a = RevF (AnnF Size (TreeF a))
type SizeRevTree a = Fix (SizeRevTreeF a)

instance (Structured RevM a, Preserving (AnnM a) f) => Preserving (AnnM a) (RevF f) where
    trans annm = AnnM getAnn'
        where
        getAnn' (RevF False bs) = runAnnM (trans annm) bs
        getAnn' (RevF True bs) = reverse (runAnnM (trans annm) bs)

instance (f ~ TreeF a) => FAlgebra f (SizeRevTree a) where
    alg = algRNat (Proxy :: Proxy (AnnM Size))

instance (f ~ TreeF a) => FCoalgebra f (SizeRevTree a) where
    coalg = coalgRNat (Proxy :: Proxy RevM)
