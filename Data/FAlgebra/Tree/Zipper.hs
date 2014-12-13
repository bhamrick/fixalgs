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

-- These were conflicting names, because they are actually the same function!
{-
left :: FCoalgebra (TreeF a) t => TreeZip a t -> TreeZip a t
left (TreeZip t p) = case coalg t of
    Empty -> TreeZip t p
    Branch a b1 b2 -> TreeZip b1 (alg $ LBranch a b2 p)

right :: FCoalgebra (TreeF a) t => TreeZip a t -> TreeZip a t
right (TreeZip t p) = case coalg t of
    Empty -> TreeZip t p
    Branch a b1 b2 -> TreeZip b2 (alg $ RBranch a b1 p)
-}

instance (a ~ a', FCoalgebra (TreeF a) t) => FCoalgebra (TreeF a') (TreeZip a t) where
    coalg (TreeZip t p) = case coalg t of
        Empty -> Empty
        Branch a b1 b2 -> Branch a
            (TreeZip b1 (alg $ LBranch a b2 p))
            (TreeZip b2 (alg $ RBranch a b1 p))

-- This could be replaced by a lens
local :: (t -> t) -> TreeZip a t -> TreeZip a t
local f (TreeZip t p) = TreeZip (f t) p

here :: TreeZip a t -> t
here (TreeZip t _) = t

root :: t -> TreeZip a t
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

insertHere :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => a -> TreeZip a t -> TreeZip a t
insertHere x (TreeZip t p) = case (coalg t :: TreeF a t) of
    Empty -> TreeZip (leaf x) p
    _     -> TreeZip t p
