{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.FAlgebra.Tree.Splay
    ( module Data.FAlgebra.Annotation
    , module Data.FAlgebra.Base
    , module Data.FAlgebra.Tree
    , module Data.FAlgebra.Tree.Indexed
    , module Data.FAlgebra.Tree.Zipper

    , getIndex
    , setIndex
    , splayStep
    , splay
    , isolateInterval
    , insertAt
    ) where

import Prelude hiding (zip)

import Data.FAlgebra.Annotation
import Data.FAlgebra.Base
import Data.FAlgebra.Tree
import Data.FAlgebra.Tree.Indexed
import Data.FAlgebra.Tree.Zipper

-- |Do one step of splaying the current node to the root. The resulting zipper is
--  focused on the same node at its new location.
splayStep :: (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
splayStep z = case directions z of
    [] -> z
    (L:[]) -> rotate z
    (R:[]) -> rotate z
    (L:L:_) -> rotate . left . rotate . up $ z
    (L:R:_) -> rotate . rotate $ z
    (R:L:_) -> rotate . rotate $ z
    (R:R:_) -> rotate . right . rotate . up $ z

-- |Splay a node all the way to the root. The resulting zipper is focused on the new root.
splay :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t) => TreeZip a t -> TreeZip a t
splay z = if isRoot z
    then z
    else splay (splayStep z)
    where
    isRoot (TreeZip _ p) = case (coalg p :: TreeZipStepF a t (TreeZipSteps a t)) of
        Root -> True
        _ -> False

-- TODO: Decide how to split indexed splays from BST splays
-- Data.FAlgebra.Tree.Splay.(Indexed|BST)?

getIndex :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t, Annotated Size t) => Int -> t -> (Maybe a, t)
getIndex i t =
    let z = idx i t
        v = value z
    in
    (v, zip . splay $ z)

setIndex :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t, Annotated Size t, Show a, Show t) => Int -> a -> t -> t
setIndex i v t =
    let z = idx i t
        z' = setValue v z
    in
    zip . splay $ z'

-- |Isolate the interval [l, r) in a rooted subtree and return a zipper for that subtree
isolateInterval :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t, Annotated Size t) => Int -> Int -> t -> TreeZip a t
isolateInterval l r t = if l >= r
    then idxSlot l t
    else let s = getSize t in
        case (l <= 0, Size r >= s) of
            (True,  True ) -> root t
            (True,  False) -> isolatePrefix r t
            (False, True ) -> isolateSuffix l t
            (False, False) -> isolateGeneral l r t
    where
    isolatePrefix :: Int -> t -> TreeZip a t
    isolatePrefix r = left . splay . idx r
    isolateSuffix :: Int -> t -> TreeZip a t
    isolateSuffix l = right . splay . idx (l-1)
    isolateGeneral :: Int -> Int -> t -> TreeZip a t
    isolateGeneral l r =
        finalizeInterval . (idx (l-1) :: t -> TreeZip a t)
        . zip . splay . (idx r :: t -> TreeZip a t)
        . zip . splay . (idx (l-1) :: t -> TreeZip a t)
        . zip . splay . (idx l :: t -> TreeZip a t)
    finalizeInterval z@(TreeZip t p) = let TreeZip t' _ = right z in
        case (coalg t' :: TreeF a t) of
            Empty -> right . rotate $ z
            _     -> right z

-- |Insert the specified element so that it is at the specified index
--  i.e. Inserting at index 0 moves every element one index up.
insertAt :: (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t, Annotated Size t) => Int -> a -> t -> t
insertAt i x = zip . splay . insertHere x . idxSlot i
