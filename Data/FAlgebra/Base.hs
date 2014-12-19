{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
-- TypeFamilies is only used for equality constraints
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.FAlgebra.Base where

import Control.Applicative
import Data.Foldable
import Data.Traversable

-- Instances can supply either a wrapped or unwrapped version
-- No fundeps because types can disambiguate instances, and fundeps
-- prevent some of the overlapping instances that we want.
class FAlgebra f a where
    alg :: f a -> a

class FCoalgebra f a where
    coalg :: a -> f a

newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

-- Catamorphism, "fold"
cata :: (Functor f, FAlgebra f a) => Fix f -> a
cata = alg . fmap cata . unFix

-- Anamorphism, "unfold"
ana :: (Functor f, FCoalgebra f a) => a -> Fix f
ana = Fix . fmap ana . coalg

-- Hylomorphism, "unfold, then fold"
hylo :: forall proxy f a b. (Functor f, FCoalgebra f a, FAlgebra f b) => proxy f -> a -> b
hylo _ = (cata :: Fix f -> b) . (ana :: a -> Fix f)

-- These use IncoherentInstances so that GHC doesn't complain when writing some general functions.
instance FAlgebra f (Fix f) where
    alg = Fix

instance FCoalgebra f (Fix f) where
    coalg = unFix

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

instance Preserving U f where
    trans _ = U

-- Maximally general in the second argument to only be tried if nothing else matches
instance (Preserving s f, Preserving t f) => Preserving (s :*: t) f where
    -- Lazy matching here is very important!
    -- Otherwise, sfix loops
    trans ~(s :*: t) = trans s :*: trans t

-- Get structure for the fixed point of a structure preserving functor
-- This is the "magic", where we create structure out of "nothing",
sfix :: (IsoRespecting s, Preserving s g) => s (Fix g)
sfix = Iso Fix unFix <$$> trans sfix

instance (IsoRespecting s, Preserving s g) => Structured s (Fix g) where
    struct = sfix

-- There are several ways for Fix g to be an f-(co)algebra.
-- The algXXX and coalgXXX functions represent the ways that I know about
-- so you just have to write an instance with the right one.
-- For recursive structures, you probably want (co)algRNat.
algPreserving :: (Functor f, Preserving (FAlgebraM f) g) => f (Fix g) -> Fix g
algPreserving = runFAlgebraM sfix

coalgPreserving :: (Functor f, Preserving (FCoalgebraM f) g) => Fix g -> f (Fix g)
coalgPreserving = runFCoalgebraM sfix

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

-- With ambiguous types, this is impossible to use because there's no way to
-- specify what structure you're using. The proxy allows us to specify that
-- at call site
algRNat :: forall proxy s f g. (Functor f, IsoRespecting s, Preserving s g, RestrictedNatural s f g) => proxy s -> f (Fix g) -> Fix g
algRNat _ = Fix . rnat (sfix :: s (Fix g))

coalgRNat :: forall proxy s f g. (Functor f, IsoRespecting s, Preserving s g, RestrictedConatural s f g) => proxy s -> Fix g -> f (Fix g)
coalgRNat _ = rconat (sfix :: s (Fix g)) . unFix

-- Maximally general restricted (co)natural instances to be tried only if
-- nothing else matches.
instance Natural f f' => RestrictedNatural s f f' where
    rnat _ = nat

instance Conatural f f' => RestrictedConatural s f f' where
    rconat _ = conat

-- Foldable and Traversable for fixed points
newtype Folder a b = Folder { runFolder :: b -> a }

instance (Functor f, FAlgebra f a) => Preserving (Folder a) f where
    trans (Folder fold) = Folder $ alg . fmap fold

-- Rank 1 version
-- f is the f-algebra
-- g is the applicative context
newtype Traverser f a g b = Traverser { runTraverser :: (f (g a) -> g a) -> b -> g a }

-- TODO: Automate this for reals
instance IsoRespecting (Traverser f a g) where
    liftIso (Iso to from) = Iso travTo travFrom
        where
        travTo (Traverser trav) = Traverser (\combine -> trav combine . from)
        travFrom (Traverser trav) = Traverser (\combine -> trav combine . to)

instance (Traversable f, Applicative g) => Preserving (Traverser f a g) f where
    -- fmap alg . sequenceA :: f (g a) -> g (f a) -> g a
    trans (Traverser trav) = Traverser $ \combine -> combine . fmap (trav combine)

-- Applicative g
-- pure :: a -> g a
-- <*> :: g (a -> b) -> g a -> g b
-- f (g a) -> g a

-- TreeF (g a) (g b) -> g (TreeF a b)
-- f' (g b) -> g (f b)
-- Produces
-- Fix f' -> g (Fix f)

{-
newtype Sequencer a g b = Sequencer { runSequencer :: b -> g a }

instance IsoRespecting (Sequencer a g) where
    liftIso (Iso to from) = Iso (Sequencer . (. from) . runSequencer) (Sequencer . (. to) . runSequencer)

instance (Traversable f, Applicative g) => Preserving (Sequencer a g) f where
    -- (b -> g a) -> (f b -> g a)
    trans (Sequencer s) = undefined
-}

-- TODO: Consider making Fix an instance of PolyKinded Functor
fmapFix :: Functor f => (forall x. f x -> f' x) -> Fix f -> Fix f'
fmapFix n = Fix . n . fmap (fmapFix n) . unFix

-- For example, when f' = TreeF (g a), f = TreeF a, this gives us Tree (g a) -> g (Tree a)
-- TODO: Consider generalizing this
sequenceFix :: forall f f' g. (Functor f, Functor g) => (forall x. f (g x) -> g (f' x)) -> Fix f -> g (Fix f')
sequenceFix semisequence = fmap Fix . semisequence . fmap (sequenceFix semisequence) . unFix

{-
class SemiSequencing g f f' where
    semisequence :: f (g a) -> g (f' a)

instance (Traversable f, Applicative g) => SemiSequencing g f f where
    semisequence = sequenceA

sequenceFix :: forall f f' g a b. (Functor f, Functor g, FCoalgebra f a, FAlgebra f' b, SemiSequencing g f f') => a -> g b
sequenceFix = fmap (alg :: f' b -> b) . semisequence . fmap sequenceFix . (coalg :: a -> f a)
-}
