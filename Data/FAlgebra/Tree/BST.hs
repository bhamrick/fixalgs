{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.FAlgebra.Tree.BST
    ( module Data.FAlgebra.Base
    , module Data.FAlgebra.Tree
    , module Data.FAlgebra.Tree.Zipper

    , find
    ) where

import Data.FAlgebra.Base
import Data.FAlgebra.Tree
import Data.FAlgebra.Tree.Zipper

-- |For a binary search tree, return either the zipper of
--  the requested element or the slot it would go if inserted.
find :: forall a t. (Ord a, FCoalgebra (TreeF a) t) => a -> t -> TreeZip a t
find x = find' x . root
    where
    find' :: a -> TreeZip a t -> TreeZip a t
    find' x z = case coalg z of
        Empty -> z
        Branch a l r -> case compare x a of
            LT -> find' x l
            EQ -> z
            GT -> find' x r
