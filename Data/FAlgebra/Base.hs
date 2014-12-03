{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
-- TypeFamilies is currently only used for equality constraints
-- It's possible it should be used everywhere, though.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- For just testing
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.FAlgebra.Base where

-- TODO: Learn about type families and see if they are a better fit

-- All fundeps are removed because they caused problems in instance declarations
-- This just means sometimes you'll need explicit type signatures.
class FAlgebra f a where
    alg :: f a -> a

class FCoalgebra f a where
    coalg :: a -> f a

newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

instance (Functor f, FAlgebra f a1, FAlgebra f a2) => FAlgebra f (a1, a2) where
    alg as = (alg (fmap fst as), alg (fmap snd as))

instance (Functor f, FCoalgebra f a1, FCoalgebra f a2) => FCoalgebra f (Either a1 a2) where
    coalg (Left a) = fmap Left (coalg a)
    coalg (Right a) = fmap Right (coalg a)
{-
class FAlgebraFixable f g | g -> f where
    algfix :: forall r. FAlgebra f r => (g r -> r) -> f (g r) -> g r

class FCoalgebraFixable f g | g -> f where
    coalgfix :: forall r. FCoalgebra f r => (r -> g r) -> g r -> f (g r)

class FAlgebraFixable f g => FAlgebraTrans f g | g -> f where
    algf :: forall r. FAlgebra f r => f (g r) -> g r

class FCoalgebraFixable f g => FCoalgebraTrans f g | g -> f where
    coalgf :: forall r. FCoalgebra f r => g r -> f (g r)
-}

newtype FAlgebraM f a = FAlgebraM { runFAlgebraM :: f a -> a }
newtype FCoalgebraM f a = FCoalgebraM { runFCoalgebraM :: a -> f a}

-- We need to be able to generalize the fixable
-- induction to additional constraints
-- s is a type constructor representing some structure.
-- For example, for f-algebras s a ~ f a -> a
class Preserving s g where
    trans :: s a -> s (g a)

-- This is a category but I'm not sure that instance is useful
data Iso a b = Iso (a -> b) (b -> a)

runIso :: Iso a b -> a -> b
runIso ~(Iso to _) = to

infixr 0 $$
($$) :: Iso a b -> a -> b
($$) = runIso

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

-- Get structure for the fixed point of a structure preserving functor
-- Fix g ~ g (Fix g)
-- trans sfix :: s (g (Fix g))
sfix :: (IsoRespecting s, Preserving s g) => s (Fix g)
sfix = liftIso (Iso Fix unFix) $$ trans sfix

-- TODO:
-- There are (at least) two useful ways of getting an FAlgebra instance for Fix g
-- If g preserves f-algebras, then we have the path
-- f (Fix g) -> f (g (Fix g)) -> g (Fix g) -> Fix g
-- Alternatively, if there is a natural transformation f -> g then we have the path
-- f (Fix g) -> g (Fix g) -> Fix g
-- I need to figure out how to support both. Probably newtypes for now :(
instance (Functor f, Preserving (FAlgebraM f) g) => FAlgebra f (Fix g) where
    alg = runFAlgebraM sfix

instance (Functor f, Preserving (FCoalgebraM f) g) => FCoalgebra f (Fix g) where
    coalg = runFCoalgebraM sfix

-- Let's try a simple F-Algebra
data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord, Functor)
type Tree a = Fix (TreeF a)

empty :: forall a t. FAlgebra (TreeF a) t => t
empty = alg (Empty :: TreeF a t)

leaf :: forall a t. FAlgebra (TreeF a) t => a -> t
leaf a = alg $ Branch a e e
    where
    e = alg (Empty :: TreeF a t)

branch :: forall a t. FAlgebra (TreeF a) t => a -> t -> t -> t
branch a b1 b2 = alg $ Branch a b1 b2
