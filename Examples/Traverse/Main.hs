{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
import Data.FAlgebra.Annotation
import Data.FAlgebra.Base
import Data.FAlgebra.Tree

import Control.Applicative (Applicative)
import Control.Monad.State

import Data.Foldable
import Data.Traversable

example :: Tree ()
example = branch () (branch () (leaf ()) (branch () empty (leaf ()))) (branch () empty (leaf ()))

type LabeledTreeF a = AnnF Int (TreeF a)
-- The newtype is because you can't partially apply type synonyms
newtype LabeledTree a = LabeledTree { runLabeledTree :: Fix (LabeledTreeF a) }
    deriving (Eq, Show)

-- TODO: Investigate ways to reduce boilerplate for newtypes
instance (Functor f, FAlgebra f (Fix (LabeledTreeF a))) => FAlgebra f (LabeledTree a) where
    alg = LabeledTree . alg . fmap runLabeledTree

instance (Functor f, FCoalgebra f (Fix (LabeledTreeF a))) => FCoalgebra f (LabeledTree a) where
    coalg = fmap LabeledTree . coalg . runLabeledTree

-- Want to define Tree a -> LabeledTree a where the label
-- on each node is its index in an inorder traversal.
-- Will work with State Int
getLabel :: State Int Int
getLabel = do
    label <- get
    modify (+1)
    return label

-- Labels empty trees with 0 and the rest with incrementing indices
labeller :: TreeF a (State Int (LabeledTree a)) -> State Int (LabeledTree a)
labeller Empty = return . LabeledTree . Fix $ AnnF 0 Empty
labeller (Branch a b1 b2) = do
    t1 <- b1
    label <- getLabel
    t2 <- b2
    return . alg $ AnnF label (Branch a t1 t2)

labelTree :: Tree a -> LabeledTree a
labelTree = flip evalState 1 . runTraverser sfix labeller

-- TODO: Can this be automated?
-- Maybe use fmapDefault from Data.Traversable?
instance Functor LabeledTree where
    -- The explicit signature on coalg t requires ScopeTypeVariables and InstanceSigs.
    -- Ugh.
    fmap :: forall a b. (a -> b) -> LabeledTree a -> LabeledTree b
    fmap f t = alg $ case (coalg t :: (LabeledTreeF a) (LabeledTree a)) of
        AnnF i Empty -> AnnF i Empty
        AnnF i (Branch a b1 b2) -> AnnF i (Branch (f a) (fmap f b1) (fmap f b2))

-- TODO: Generalize Folder like Traverser
instance Foldable LabeledTree where
    -- foldMap :: Monoid m => (a -> m) -> t a -> m
    foldMap = undefined

algCombine :: (FAlgebra f a, Traversable f, Applicative g) => f (g a) -> g a
algCombine = fmap alg . sequenceA

-- TODO: Make this work properly
instance Traversable LabeledTree where
    -- traverse :: Applicative g => (a -> g b) -> t a -> g (t b)
    traverse = undefined -- runTraverser sfix algCombine

main :: IO ()
main = do
    print example
    print . labelTree $ example
