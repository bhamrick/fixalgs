{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
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

-- |Traversal for the value of a node.
_node :: Applicative f => LensLike f (TreeF a b) (TreeF a' b) a a'
_node _ Empty = pure Empty
_node f (Branch a b1 b2) = fmap (\a' -> Branch a' b1 b2) (f a)
{-# INLINE _node #-}

-- |Traversal for the left branch of a node. Can't change type because left and right need to stay the same type.
_left :: Applicative f => LensLike' f (TreeF a b) b
_left _ Empty = pure Empty
_left f (Branch a b1 b2) = fmap (\b1' -> Branch a b1' b2) (f b1)
{-# INLINE _left #-}

-- |Traversal for the right branch of a node. Can't change type because left and right need to stay the same type.
_right :: Applicative f => LensLike' f (TreeF a b) b
_right _ Empty = pure Empty
_right f (Branch a b1 b2) = fmap (Branch a b1) (f b2)
{-# INLINE _right #-}

-- |Traversal for both children of a node.
_children :: Applicative f => LensLike f (TreeF a b) (TreeF a b') b b'
_children _ Empty = pure Empty
_children f (Branch a b1 b2) = Branch a <$> f b1 <*> f b2
{-# INLINE _children #-}

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

instance Functor Tree where
    fmap f = Tree . fmapFix (over _node f) . runTree

-- |Create a tree from its node and its children
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
