{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
import Data.FAlgebra.Annotation
import Data.FAlgebra.Base
import Data.FAlgebra.Tree

import Control.Applicative (Applicative, (<$>), (<*>), pure)
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

-- TODO: Can this be written as a real traversal?
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

-- TODO: Can this be simplified further?
instance Functor LabeledTree where
    fmap f = LabeledTree . fmapFix n . runLabeledTree
        where
        n (AnnF i Empty) = AnnF i Empty
        n (AnnF i (Branch a b1 b2)) = AnnF i (Branch (f a) b1 b2)

-- TODO: Generalize Folder like Traverser
instance Foldable LabeledTree where
    -- foldMap :: Monoid m => (a -> m) -> t a -> m
    foldMap = undefined

algCombine :: (FAlgebra f a, Traversable f, Applicative g) => f (g a) -> g a
algCombine = fmap alg . sequenceA

-- TODO: Make lenses for annotation
instance Traversable LabeledTree where
    -- sequenceA :: Applicative g => LabeledTree (g a) -> g (LabeledTree a)
    sequenceA = fmap LabeledTree . sequenceFix semisequence . runLabeledTree
        where
        semisequence :: Applicative g => LabeledTreeF (g a) (g b) -> g (LabeledTreeF a b)
        semisequence (AnnF i Empty) = pure (AnnF i Empty)
        semisequence (AnnF i (Branch a b1 b2)) = (\x y z ->
            AnnF i (Branch y x z)) <$> b1 <*> a <*> b2

main :: IO ()
main = do
    print example
    print . labelTree $ example
