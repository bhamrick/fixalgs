{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Data.FAlgebra.Hole 
    ( module Data.FAlgebra.Base
    , HoleF(..)
    , HoleM(..)
    ) where

import Data.FAlgebra.Base
import Data.Functor

-- |Transform a functor to allow holes of type a
data HoleF a f r = Hole a | Full (f r)
    deriving (Eq, Show, Functor)

instance Natural f f' => Natural f (HoleF a f') where
    nat = Full . nat

instance RestrictedNatural s f f' => RestrictedNatural s f (HoleF a f') where
    rnat s = Full . rnat s

-- |Hole filling structure
--  This isn't quite the dual of what I have for annotations
--  But it definitely makes more sense here so maybe I was wrong
--  with annotations.
--  Note that when a is an f-coalgebra we can make a -> f r
--  from a -> t through a -> f a -> f r
newtype HoleM a f r = HoleM { runHoleM :: a -> f r }

instance (Functor f, Conatural f f') => RestrictedConatural (HoleM a f) f (HoleF a f') where
    rconat (HoleM fillHole) (Hole a) = fillHole a
    rconat (HoleM fillHole) (Full bs) = conat bs

instance (Functor f, RestrictedConatural s f f') => RestrictedConatural (s :*: HoleM a f) f (HoleF a f') where
    rconat (s :*: HoleM fillHole) (Hole a) = fillHole a
    rconat (s :*: _) (Full bs) = rconat s bs

-- Does this instance make sense?
instance Functor f => Preserving (HoleM a f) (HoleF a f) where
    trans (HoleM fillHole) = HoleM (\a -> const (Hole a) <$> fillHole a)
