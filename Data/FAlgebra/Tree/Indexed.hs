{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.FAlgebra.Tree.Indexed where

import Prelude hiding (zip)

import Control.Applicative (Const(..), getConst)

import Data.FAlgebra.Annotation
import Data.FAlgebra.Base
import Data.FAlgebra.Tree
import Data.FAlgebra.Tree.Zipper

import Lens.Micro

-- |Get a zipper for the ith element of a tree.
idx :: forall a t. (FCoalgebra (TreeF a) t, Annotated Size t) => Int -> t -> TreeZip a t
idx i = idx' (Size i) . root
    where
    idx' i z = case (coalg z :: TreeF a (TreeZip a t)) of
        Empty -> z
        Branch a b1 b2 -> let s = getSize (view _here b1) in
            case compare i s of
                LT -> idx' i b1
                EQ -> z
                GT -> idx' (i - s - 1) b2

-- |Get a zipper the slot such that inserting there makes the inserted element the ith element.
idxSlot :: forall a t. (FCoalgebra (TreeF a) t, Annotated Size t) => Int -> t -> TreeZip a t
idxSlot i = idxSlot' (Size i) . root
    where
    idxSlot' i z = case (coalg z :: TreeF a (TreeZip a t)) of
        Empty -> z
        Branch _ b1 b2 -> let s = getSize (view _here b1) in
            case compare i s of
                LT -> idxSlot' i b1
                EQ -> idxSlot' i b1
                GT -> idxSlot' (i - s - 1) b2
