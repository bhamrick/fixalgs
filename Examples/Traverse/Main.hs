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

-- TODO: Can this be simplified further?
instance Functor LabeledTree where
    fmap f = LabeledTree . fmapFix n . runLabeledTree
        where
        n (AnnF i Empty) = AnnF i Empty
        n (AnnF i (Branch a b1 b2)) = AnnF i (Branch (f a) b1 b2)

algCombine :: (FAlgebra f a, Traversable f, Applicative g) => f (g a) -> g a
algCombine = fmap alg . sequenceA

instance Traversable LabeledTree where
    -- sequenceA :: Applicative g => LabeledTree (g a) -> g (LabeledTree a)
    sequenceA = fmap LabeledTree . sequenceFix semisequence . runLabeledTree
        where
        semisequence :: Applicative g => LabeledTreeF (g a) (g b) -> g (LabeledTreeF a b)
        semisequence (AnnF i Empty) = pure (AnnF i Empty)
        semisequence (AnnF i (Branch a b1 b2)) = (\x y z ->
            AnnF i (Branch y x z)) <$> b1 <*> a <*> b2

instance Foldable LabeledTree where
    foldMap = foldMapDefault

instance Traversable Tree where
    sequenceA = fmap Tree . sequenceFix inorder . runTree
        where
        inorder :: Applicative g => TreeF (g a) (g b) -> g (TreeF a b)
        inorder Empty = pure Empty
        inorder (Branch a b1 b2) = (\x y z -> Branch y x z) <$> b1 <*> a <*> b2

instance Foldable Tree where
    foldMap = foldMapDefault

labelStep :: a -> State Int (Int, a)
labelStep a = (,) <$> getLabel <*> pure a

-- TODO: Determine if there's a better type signature/implementation that
-- generalizes better
annotateFromPair :: x -> TreeF (x, a) b -> AnnF x (TreeF a) b
annotateFromPair def Empty = AnnF def Empty
annotateFromPair _ (Branch (x, a) b1 b2) = AnnF x (Branch a b1 b2)

-- Label empty trees with 0 and others with their index in an inorder traversal
-- Follows the type path
-- Tree a -> State Int (Tree (Int, a)) -> Tree (Int, a) -> State Int (LabeledTree a)
labelTree :: Tree a -> LabeledTree a
labelTree = LabeledTree . fmapFix (annotateFromPair 0) . runTree . flip evalState 1 . traverse labelStep

-- I should be able to write
-- Something like
-- Applicative g => (forall b. f b -> g a) -> Fix f -> g (Fix (AnnF a f))
-- But I need traversal order also, and f should be able to change to a different functor.
-- Certainly I can write
-- (Applicative g, Traversable f) => (forall b. f b -> g a) -> Fix f -> g (Fix (AnnF a f))
-- But this doesn't traverse over internal data (which requires transforming TreeF (g a) to TreeF a)
-- I also need the semisequence :: forall b. f (g b) -> g (f' b)

labelStep' :: TreeF a b -> State Int Int
labelStep' Empty = return 0
labelStep' (Branch _ _ _) = getLabel

main :: IO ()
main = do
    print example
    print . labelTree $ example
