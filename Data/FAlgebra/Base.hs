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

-- |Typeclass for F-Algebras. In most cases, the surrounding types will
--  disambiguate which instance, but sometimes an explicit type signature
--  and possibly the ScopedTypeVariables extension will be necessary.
class FAlgebra f a where
    alg :: f a -> a

-- |Typeclass for F-Coalgebras. In most cases, the surrounding types will
--  disambiguate which instance, but sometimes an explicit type signature
--  and possibly the ScopedTypeVariables extension will be necessary.
class FCoalgebra f a where
    coalg :: a -> f a

-- |The fixed point type for a functor.
newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

-- |Catamorphism, "fold"
cata :: (Functor f, FAlgebra f a) => Fix f -> a
cata = alg . fmap cata . unFix

-- |Anamorphism, "unfold"
ana :: (Functor f, FCoalgebra f a) => a -> Fix f
ana = Fix . fmap ana . coalg

-- |Hylomorphism, "unfold, then fold". Requires a proxy to know which Fix f to factor through.
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

-- |Data representation of an F-Algebra
newtype FAlgebraM f a = FAlgebraM { runFAlgebraM :: f a -> a }
-- |Data representation of an F-Coalgebra
newtype FCoalgebraM f a = FCoalgebraM { runFCoalgebraM :: a -> f a}

-- |Product of two type constructors.
data (f :*: g) a = (f a) :*: (g a)

-- |Extract the first constructor from a product
pfst :: (f :*: g) a -> f a
pfst ~(x :*: _) = x

-- |Extract the second constructor from a product
psnd :: (f :*: g) a -> g a
psnd ~(_ :*: y) = y

-- |Unit functor, identity for :*:
data U a = U
    deriving (Eq, Show, Ord)

instance Functor U where
    fmap _ U = U

-- |Class for structured types, parameteriezd by the type of structure.
class Structured s a where
    struct :: s a

-- |Class for functors that preserve some structure.
class Preserving s g where
    trans :: s a -> s (g a)

instance (Structured s a, Preserving s g) => Structured s (g a) where
    struct = trans struct

-- This is a category but I'm not sure that instance is useful

data Iso a b = Iso (a -> b) (b -> a)

runIso :: Iso a b -> a -> b
runIso ~(Iso to _) = to

infixr 0 $$
-- |Infix version of runIso
($$) :: Iso a b -> a -> b
($$) = runIso

invert :: Iso a b -> Iso b a
invert (Iso f g) = Iso g f

-- |Class for structures that respect isomorphisms
class IsoRespecting s where
    liftIso :: Iso a b -> Iso (s a) (s b)

infixr 2 <$$>
-- |Push an isomorphism through an isomorphism respecting structure
(<$$>) :: IsoRespecting s => Iso a b -> s a -> s b
(<$$>) = runIso . liftIso

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

-- |Get structure for the fixed point of a structure preserving functor
--  This is the "magic", where we create structure out of "nothing".
sfix :: (IsoRespecting s, Preserving s g) => s (Fix g)
sfix = Iso Fix unFix <$$> trans sfix

instance (IsoRespecting s, Preserving s g) => Structured s (Fix g) where
    struct = sfix

-- There are several ways for Fix g to be an f-(co)algebra.
-- The algXXX and coalgXXX functions represent the ways that I know about
-- so you just have to write an instance with the right one.
-- For recursive structures, you probably want (co)algRNat.

-- |An f-algebra definition for Fix g when g preserves f-algebras.
--  Generally, algNat or algRNat will be a better choice.
algPreserving :: (Functor f, Preserving (FAlgebraM f) g) => f (Fix g) -> Fix g
algPreserving = runFAlgebraM sfix

-- |An f-coalgebra definition for Fix g when g preserves f-coalgebras.
--  Generally, coalgNat or coalgRNat will be a better choice.
coalgPreserving :: (Functor f, Preserving (FCoalgebraM f) g) => Fix g -> f (Fix g)
coalgPreserving = runFCoalgebraM sfix

-- TODO: Consider making these data parameters rather than type classes.
class Natural f g where
    nat :: f r -> g r

class Conatural f g where
    conat :: g r -> f r

instance (Functor f, f ~ f') => Natural f f' where
    nat = id

instance (Functor f, f ~ f') => Conatural f f' where
    conat = id

-- |Defines an f-algebra for Fix g when there is a natural transformation f -> g
algNat :: (Functor f, Natural f g) => f (Fix g) -> Fix g
algNat = Fix . nat

-- |Defines an f-coalgebra for Fix g when there is a natural transformation g -> f
coalgNat :: (Functor f, Conatural f g) => Fix g -> f (Fix g)
coalgNat = conat . unFix

-- |Restricted Natural class
--  These are natural transformations between functors that only work when the base
--  type has sufficient structure
class RestrictedNatural s f f' where
    rnat :: s a -> f a -> f' a

class RestrictedConatural s f f' where
    rconat :: s a -> f' a -> f a

-- With ambiguous types, this is impossible to use because there's no way to
-- specify what structure you're using. The proxy allows us to specify that
-- at call site

-- |Defines an f-algebra for Fix g when there is a restricted natural transformation
--  f -> g requiring some structure s. The proxy is used to disambiguate what structure
--  to use.
algRNat :: forall proxy s f g. (Functor f, IsoRespecting s, Preserving s g, RestrictedNatural s f g) => proxy s -> f (Fix g) -> Fix g
algRNat _ = Fix . rnat (sfix :: s (Fix g))

-- |Defines an f-coalgebra for Fix g when there is a restricted natural transformation
--  g -> f requiring some structure s. The proxy is used to disambiguate what structure
--  to use.
coalgRNat :: forall proxy s f g. (Functor f, IsoRespecting s, Preserving s g, RestrictedConatural s f g) => proxy s -> Fix g -> f (Fix g)
coalgRNat _ = rconat (sfix :: s (Fix g)) . unFix

-- |Version of algNat/algRNat that takes the natural transformation as an input.
algNat' :: (f (Fix g) -> g (Fix g)) -> f (Fix g) -> Fix g
algNat' n = Fix . n

-- |Version of coalgNat/coalgRNat that takes the natural transformation as an input.
coalgNat' :: (g (Fix g) -> f (Fix g)) -> Fix g -> f (Fix g)
coalgNat' cn = cn . unFix

-- Maximally general restricted (co)natural instances to be tried only if
-- nothing else matches.
instance Natural f f' => RestrictedNatural s f f' where
    rnat _ = nat

instance Conatural f f' => RestrictedConatural s f f' where
    rconat _ = conat

-- These two functions can be used to define Foldable and Traversable instances

-- Fix is a functor from Functors in (* -> *) to *
-- The first argument of fmapFix should be a natural transformation,
-- but we only need to apply it on Fix f'.
-- We could also define fmapFix only applying it to Fix f.

-- |Turn a natural transformation (or similar) into a map between fixed points.
fmapFix :: Functor f => (f (Fix f') -> f' (Fix f')) -> Fix f -> Fix f'
fmapFix n = Fix . n . fmap (fmapFix n) . unFix

-- For example, when f' = TreeF (g a), f = TreeF a, this gives us Tree (g a) -> g (Tree a)
-- Note that when g = Identity this reduces to fmapFix.

-- Similarly here, the first argument is generally going to be of the form
-- forall x. f (g x) -> g (f' x)
-- but we only need to apply it with x = Fix f'
-- We don't require the full polymorphism because sometimes it needs an additional constraint on x.

-- |More general mapping between fixed points, where we pull a functor out through the input.
sequenceFix :: (Functor f, Functor g) => (f (g (Fix f')) -> g (f' (Fix f'))) -> Fix f -> g (Fix f')
sequenceFix semisequence = fmap Fix . semisequence . fmap (sequenceFix semisequence) . unFix
