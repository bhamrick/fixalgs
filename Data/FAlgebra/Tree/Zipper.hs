{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Data.FAlgebra.Tree.Zipper where

import Prelude hiding (zip)
import Data.FAlgebra.Base
import Data.FAlgebra.Annotation
import Data.FAlgebra.Tree hiding (left, right)

-- |Unfixed version of the list of steps up the tree
--  LBranch means that the current tree is a left child
--  RBranch means that the current tree is a right child
data TreeZipStepF a t b = Root
                        | LBranch a t b
                        | RBranch a t b
    deriving (Eq, Show, Functor)

type TreeZipSteps a t = Fix (TreeZipStepF a t)

data TreeDirection = L | R
    deriving (Eq, Show, Ord)

instance (f ~ TreeZipStepF a t) => FAlgebra f (TreeZipSteps a t) where
    alg = algNat

instance (f ~ TreeZipStepF a t) => FCoalgebra f (TreeZipSteps a t) where
    coalg = coalgNat

data TreeZip a t = TreeZip t (TreeZipSteps a t)
    deriving (Eq, Show)

-- |Extract the value at a zipper's current location (if any)
value :: FCoalgebra (TreeF a) t => TreeZip a t -> Maybe a
value (TreeZip t _) = case coalg t of
    Empty -> Nothing
    Branch a _ _ -> Just a

-- |Move up in the tree, staying still if at the root.
-- left and right come from the coalgebra instance for TreeZip a t.
up :: FAlgebra (TreeF a) t => TreeZip a t -> TreeZip a t
up (TreeZip t p) = case coalg p of
    Root -> TreeZip t p
    LBranch a t' p' -> TreeZip (branch a t t') p'
    RBranch a t' p' -> TreeZip (branch a t' t) p'

-- Zippers have a natural F-Coalgebra structure
-- This allows us to use `left` and `right` for zippers as well.
instance (a ~ a', FCoalgebra (TreeF a) t) => FCoalgebra (TreeF a') (TreeZip a t) where
    coalg (TreeZip t p) = case coalg t of
        Empty -> Empty
        Branch a b1 b2 -> Branch a
            (TreeZip b1 (alg $ LBranch a b2 p))
            (TreeZip b2 (alg $ RBranch a b1 p))

-- |Lens for the current subtree
_here :: Functor f => (t -> f t) -> TreeZip a t -> f (TreeZip a t)
_here f (TreeZip t p) = fmap (flip TreeZip p) (f t)
{-# INLINE _here #-}

-- |Get a zipper for the root of a tree
root :: t -> TreeZip a t
root t = TreeZip t (alg Root)

-- |Zip up a zipper into a tree
zip :: FAlgebra (TreeF a) t => TreeZip a t -> t
zip z@(TreeZip t p) = if isRoot z
    then t
    else zip (up z)
    where
    isRoot (TreeZip _ p) = case coalg p of
        Root -> True
        _ -> False

-- |Move to the current node's sibling. Stays still at the root.
sibling :: (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
sibling (TreeZip t p) = case coalg p of
    Root -> TreeZip t p
    LBranch a t' p' -> TreeZip t' (alg $ RBranch a t p')
    RBranch a t' p' -> TreeZip t' (alg $ LBranch a t p')

-- |Get the list of directions on the path up to the root.
--  The head of the list corresponds to the current node's relation to its parent,
--  so we're a left child if the head is L, for example.
directions :: forall a t. TreeZip a t -> [TreeDirection]
directions (TreeZip _ p) = directions' p
    where
    directions' p = case (coalg p :: TreeZipStepF a t (TreeZipSteps a t)) of
        Root -> []
        LBranch _ _ p' -> L : directions' p'
        RBranch _ _ p' -> R : directions' p'

-- |Rotate the current node to its parents position.
--  Does nothing if at the root of the tree.
rotate :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
rotate z@(TreeZip t p) = case coalg p of
    Root -> z
    LBranch a' t' p' -> case (coalg t :: TreeF a t) of
        Empty -> z
        Branch a l r -> TreeZip (branch a l (branch a' r t')) p'
    RBranch a' t' p' -> case (coalg t :: TreeF a t) of
        Empty -> z
        Branch a l r -> TreeZip (branch a (branch a' t' l) r) p'

-- |Insert a tree into the current zipper location if it's empty.
insertHere :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => a -> TreeZip a t -> TreeZip a t
insertHere x (TreeZip t p) = case (coalg t :: TreeF a t) of
    Empty -> TreeZip (leaf x) p
    _     -> TreeZip t p
