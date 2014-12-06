{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
-- TypeFamilies is currently only used for equality constraints
-- It's possible it should be used everywhere, though.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.FAlgebra.Base where

import Data.Proxy

-- TODO: Learn about type families and see if they are a better fit

-- All fundeps are removed because they caused problems in instance declarations
-- This just means sometimes you'll need explicit type signatures.

-- Instances can supply either a wrapped or unwrapped version
class FAlgebra f a where
    alg :: f a -> a
    algM :: FAlgebraM f a

    algM = FAlgebraM alg
    alg = runFAlgebraM algM

class FCoalgebra f a where
    coalg :: a -> f a
    coalgM :: FCoalgebraM f a

    coalgM = FCoalgebraM coalg
    coalg = runFCoalgebraM coalgM

newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

instance (Functor f, FAlgebra f a1, FAlgebra f a2) => FAlgebra f (a1, a2) where
    alg as = (alg (fmap fst as), alg (fmap snd as))

instance (Functor f, FCoalgebra f a1, FCoalgebra f a2) => FCoalgebra f (Either a1 a2) where
    coalg (Left a) = fmap Left (coalg a)
    coalg (Right a) = fmap Right (coalg a)

newtype FAlgebraM f a = FAlgebraM { runFAlgebraM :: f a -> a }
newtype FCoalgebraM f a = FCoalgebraM { runFCoalgebraM :: a -> f a}

data (f :*: g) a = (f a) :*: (g a)

pfst :: (f :*: g) a -> f a
pfst (x :*: _) = x

psnd :: (f :*: g) a -> g a
psnd (_ :*: y) = y

-- Unit functor, identity for :*:
-- Isomorphic to Const ()
data U a = U
    deriving (Eq, Show, Ord)

instance Functor U where
    fmap _ U = U

class Structured s a where
    struct :: s a

-- We need to be able to generalize the fixable
-- induction to additional constraints
-- s is a type constructor representing some structure.
-- For example, for f-algebras s a ~ f a -> a
class Preserving s g where
    trans :: s a -> s (g a)

instance (Structured s a, Preserving s g) => Structured s (g a) where
    struct = trans struct

-- This is a category but I'm not sure that instance is useful
data Iso a b = Iso (a -> b) (b -> a)

runIso :: Iso a b -> a -> b
runIso ~(Iso to _) = to

infixr 0 $$
($$) :: Iso a b -> a -> b
($$) = runIso

infixr 2 <$$>
(<$$>) :: IsoRespecting s => Iso a b -> s a -> s b
(<$$>) = runIso . liftIso

invert :: Iso a b -> Iso b a
invert (Iso f g) = Iso g f

-- TODO: Should this just be a 4 parameter type family?
-- So that we can lift an iso to the type (f a -> a) directly,
-- rather than to FAlgebraM, for example.
class IsoRespecting s where
    liftIso :: Iso a b -> Iso (s a) (s b)

instance Functor f => IsoRespecting (FAlgebraM f) where
    liftIso (Iso to from) = Iso algTo algFrom
        where
        algTo (FAlgebraM alg) = FAlgebraM (to . alg . fmap from)
        algFrom (FAlgebraM alg) = FAlgebraM (from . alg . fmap to)

instance (Functor f, f ~ f') => Preserving (FAlgebraM f) f' where
    trans = FAlgebraM . fmap . runFAlgebraM

instance Functor f => IsoRespecting (FCoalgebraM f) where
    liftIso (Iso to from) = Iso coalgTo coalgFrom
        where
        coalgTo (FCoalgebraM coalg) = FCoalgebraM (fmap to . coalg . from)
        coalgFrom (FCoalgebraM coalg) = FCoalgebraM (fmap from . coalg . to)

instance (Functor f, f ~ f') => Preserving (FCoalgebraM f) f' where
    trans = FCoalgebraM . fmap . runFCoalgebraM

instance (Functor f, Functor g) => Functor (f :*: g) where
    fmap f ~(xs :*: ys) = fmap f xs :*: fmap f ys

instance IsoRespecting U where
    liftIso iso = Iso uTo uFrom
        where
        uTo _ = U
        uFrom _ = U

instance (IsoRespecting f, IsoRespecting g) => IsoRespecting (f :*: g) where
    liftIso iso = Iso pTo pFrom
        where
        pTo ~(x :*: y) = (iso <$$> x) :*: (iso <$$> y)
        pFrom ~(x :*: y) = (invert iso <$$> x) :*: (invert iso <$$> y)

-- This is not maximally general because we want it to be applied whenever s is U
instance Preserving U f where
    trans _ = U

-- Maximally general in the second argument to only be tried if nothing else matches
instance (Preserving s f, Preserving t f) => Preserving (s :*: t) f where
    -- Lazy matching here is very important!
    -- Otherwise, sfix loops
    trans ~(s :*: t) = trans s :*: trans t

-- Get structure for the fixed point of a structure preserving functor
-- Fix g ~ g (Fix g)
-- trans sfix :: s (g (Fix g))
sfix :: (IsoRespecting s, Preserving s g) => s (Fix g)
sfix = Iso Fix unFix <$$> trans sfix

instance (IsoRespecting s, Preserving s g) => Structured s (Fix g) where
    struct = sfix

algPreserving :: (Functor f, Preserving (FAlgebraM f) g) => f (Fix g) -> Fix g
algPreserving = runFAlgebraM sfix

coalgPreserving :: (Functor f, Preserving (FCoalgebraM f) g) => Fix g -> f (Fix g)
coalgPreserving = runFCoalgebraM sfix

-- There are (at least) two useful ways of getting an FAlgebra instance for Fix g
-- If g preserves f-algebras, then we have the path
-- f (Fix g) -> f (g (Fix g)) -> g (Fix g) -> Fix g
-- Alternatively, if there is a natural transformation f -> g then we have the path
-- f (Fix g) -> g (Fix g) -> Fix g

-- The new solution is to use plain old functions that you can put in instance declarations
-- for your actual datatypes

class Natural f g where
    nat :: f r -> g r

class Conatural f g where
    conat :: g r -> f r

instance (Functor f, f ~ f') => Natural f f' where
    nat = id

instance (Functor f, f ~ f') => Conatural f f' where
    conat = id

algNat :: (Functor f, Natural f g) => f (Fix g) -> Fix g
algNat = Fix . nat

coalgNat :: (Functor f, Conatural f g) => Fix g -> f (Fix g)
coalgNat = conat . unFix

-- Restricted Natural classes
-- These are natural transformations between functors that only work when the base
-- type has sufficient structure
class RestrictedNatural s f f' where
    rnat :: s a -> f a -> f' a

class RestrictedConatural s f f' where
    rconat :: s a -> f' a -> f a

-- With ambiguous types, this is impossible to use
-- We'll just take a proxy so that the structure can be specified
-- at call site
algRNat :: forall s f g. (Functor f, IsoRespecting s, Preserving s g, RestrictedNatural s f g) => Proxy s -> f (Fix g) -> Fix g
algRNat _ = Fix . rnat (sfix :: s (Fix g))

coalgRNat :: forall s f g. (Functor f, IsoRespecting s, Preserving s g, RestrictedConatural s f g) => Proxy s -> Fix g -> f (Fix g)
coalgRNat _ = rconat (sfix :: s (Fix g)) . unFix

-- Maximally general restricted (co)natural instances
instance (s ~ U, f ~ f') => RestrictedNatural s f f' where
    rnat _ = id

instance (s ~ U, f ~ f') => RestrictedConatural s f f' where
    rconat _ = id
