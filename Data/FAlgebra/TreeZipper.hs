{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Data.FAlgebra.TreeZipper where

import Prelude hiding (zip)
import Data.FAlgebra.Base
import Data.FAlgebra.Annotation
import Data.FAlgebra.Tree hiding (left, right)

-- I don't know if there's a point to this being unfixed
-- LBranch means that the current tree is a left child
-- RBranch means that the current tree is a right child
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

value :: FCoalgebra (TreeF a) t => TreeZip a t -> Maybe a
value (TreeZip t _) = case coalg t of
    Empty -> Nothing
    Branch a _ _ -> Just a

up :: FAlgebra (TreeF a) t => TreeZip a t -> TreeZip a t
up (TreeZip t p) = case coalg p of
    Root -> TreeZip t p
    LBranch a t' p' -> TreeZip (branch a t t') p'
    RBranch a t' p' -> TreeZip (branch a t' t) p'

left :: FCoalgebra (TreeF a) t => TreeZip a t -> TreeZip a t
left (TreeZip t p) = case coalg t of
    Empty -> TreeZip t p
    Branch a b1 b2 -> TreeZip b1 (alg $ LBranch a b2 p)

right :: FCoalgebra (TreeF a) t => TreeZip a t -> TreeZip a t
right (TreeZip t p) = case coalg t of
    Empty -> TreeZip t p
    Branch a b1 b2 -> TreeZip b2 (alg $ RBranch a b1 p)

-- Constraint is just to remove explicit type signatures
root :: FCoalgebra (TreeF a) t => t -> TreeZip a t
root t = TreeZip t (alg Root)

zip :: FAlgebra (TreeF a) t => TreeZip a t -> t
zip z@(TreeZip t p) = if isRoot z
    then t
    else zip (up z)
    where
    isRoot (TreeZip _ p) = case coalg p of
        Root -> True
        _ -> False

sibling :: (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
sibling (TreeZip t p) = case coalg p of
    Root -> TreeZip t p
    LBranch a t' p' -> TreeZip t' (alg $ RBranch a t p')
    RBranch a t' p' -> TreeZip t' (alg $ LBranch a t p')

directions :: forall a t. TreeZip a t -> [TreeDirection]
directions (TreeZip _ p) = directions' p
    where
    directions' p = case (coalg p :: TreeZipStepF a t (TreeZipSteps a t)) of
        Root -> []
        LBranch _ _ p' -> L:(directions' p')
        RBranch _ _ p' -> R:(directions' p')

rotate :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
rotate z@(TreeZip t p) = case coalg p of
    Root -> z
    LBranch a' t' p' -> case (coalg t :: TreeF a t) of
        Empty -> z
        Branch a l r -> TreeZip (branch a l (branch a' r t')) p'
    RBranch a' t' p' -> case (coalg t :: TreeF a t) of
        Empty -> z
        Branch a l r -> TreeZip (branch a (branch a' t' l) r) p'

splayStep :: (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
splayStep z = case directions z of
    [] -> z
    (L:[]) -> rotate z
    (R:[]) -> rotate z
    (L:L:_) -> rotate . left . rotate . up $ z
    (L:R:_) -> rotate . rotate $ z
    (R:L:_) -> rotate . rotate $ z
    (R:R:_) -> rotate . right . rotate . up $ z

splay :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
splay z = if isRoot z
    then z
    else splay (splayStep z)
    where
    isRoot (TreeZip _ p) = case (coalg p :: TreeZipStepF a t (TreeZipSteps a t)) of
        Root -> True
        _ -> False

idx :: forall a t. (FCoalgebra (TreeF a) t, Structured (AnnM Size) t) => Int -> t -> TreeZip a t
idx i = idx' (Size i) . root
    where
    idx' i z@(TreeZip t _) = case (coalg t :: TreeF a t) of
        Empty -> z
        Branch a b1 b2 -> let s = getSize b1 in
            case compare i s of
                LT -> idx' i (left z)
                EQ -> z
                GT -> idx' (i - s - 1) (right z)

-- Returns the slot such that if you insert there then the
-- inserted element will be the specified index
idxSlot :: forall a t. (FCoalgebra (TreeF a) t, Structured (AnnM Size) t) => Int -> t -> TreeZip a t
idxSlot i = idxSlot' (Size i) . root
    where
    idxSlot' i z@(TreeZip t _) = case (coalg t :: TreeF a t) of
        Empty -> z
        Branch _ b1 b2 -> let s = getSize b1 in
            case compare i s of
                LT -> idxSlot' i (left z)
                EQ -> idxSlot' i (left z)
                GT -> idxSlot' (i - s - 1) (right z)

-- For a binary search tree, return either the zipper of
-- the requested element or the slot it would go if inserted.
find :: forall a t. (Ord a, FCoalgebra (TreeF a) t) => a -> t -> TreeZip a t
find x = find' x . root
    where
    find' :: (Ord a, FCoalgebra (TreeF a) t) => a -> TreeZip a t -> TreeZip a t
    find' x z@(TreeZip t _) = case (coalg t :: TreeF a t) of
        Empty -> z
        Branch a _ _ -> case compare x a of
            LT -> find' x (left z)
            EQ -> z
            GT -> find' x (right z)

insert' :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => a -> TreeZip a t -> TreeZip a t
insert' x (TreeZip t p) = case (coalg t :: TreeF a t) of
    Empty -> TreeZip (leaf x) p
    _     -> TreeZip t p

-- Inserts the specified element so that it is at the specified index
-- i.e. Inserting at index 0 moves every element one index up.
insertAt :: (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t, Structured (AnnM Size) t) => Int -> a -> t -> t
insertAt i x = zip . splay . insert' x . idxSlot i
