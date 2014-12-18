{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
import Data.FAlgebra.Annotation
import Data.FAlgebra.Base
import Data.FAlgebra.Tree

import Control.Monad.State

example :: Tree ()
example = branch () (branch () (leaf ()) (branch () empty (leaf ()))) (branch () empty (leaf ()))

type LabeledTreeF a = AnnF Int (TreeF a)
type LabeledTree a = Fix (LabeledTreeF a)

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
labeller Empty = return . Fix $ AnnF 0 Empty
labeller (Branch a b1 b2) = do
    t1 <- b1
    label <- getLabel
    t2 <- b2
    return . alg $ AnnF label (Branch a t1 t2)

labelTree :: Tree a -> LabeledTree a
labelTree = flip evalState 1 . runTraverser sfix labeller

main :: IO ()
main = do
    print example
    print . labelTree $ example
