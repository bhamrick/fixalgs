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

-- Get structure for the fixed point of a structure preserving functor
-- Fix g ~ g (Fix g)
-- trans sfix :: s (g (Fix g))
sfix :: (IsoRespecting s, Preserving s g) => s (Fix g)
sfix = Iso Fix unFix <$$> trans sfix

-- TODO:
-- There are (at least) two useful ways of getting an FAlgebra instance for Fix g
-- If g preserves f-algebras, then we have the path
-- f (Fix g) -> f (g (Fix g)) -> g (Fix g) -> Fix g
-- Alternatively, if there is a natural transformation f -> g then we have the path
-- f (Fix g) -> g (Fix g) -> Fix g
-- I need to figure out how to support both. Probably newtypes for now :(

-- We use newtypes to distinguish the method of constructing a (co)-algebra
-- for the fixed point of a functor. Datatypes can use these to define the proper
-- instances for Fix g itself.
newtype TransFix f = TransFix { runTransFix :: Fix f }
deriving instance Eq (f (Fix f)) => Eq (TransFix f)
deriving instance Show (f (Fix f)) => Show (TransFix f)

instance (Functor f, Preserving (FAlgebraM f) g) => FAlgebra f (TransFix g) where
    algM = Iso TransFix runTransFix <$$> sfix

instance (Functor f, Preserving (FCoalgebraM f) g) => FCoalgebra f (TransFix g) where
    coalgM = Iso TransFix runTransFix <$$> sfix

class Natural f g where
    nat :: f r -> g r

class Conatural f g where
    conat :: g r -> f r

instance (Functor f, f ~ f') => Natural f f' where
    nat = id

instance (Functor f, f ~ f') => Conatural f f' where
    conat = id

newtype NatFix f = NatFix { runNatFix :: Fix f }
deriving instance Eq (f (Fix f)) => Eq (NatFix f)
deriving instance Show (f (Fix f)) => Show (NatFix f)

instance (Functor f, Natural f g) => FAlgebra f (NatFix g) where
    algM = Iso NatFix runNatFix <$$> FAlgebraM (Fix . nat)

instance (Functor f, Conatural f g) => FCoalgebra f (NatFix g) where
    coalgM = Iso NatFix runNatFix <$$> FCoalgebraM (conat . unFix)

-- Let's try a simple F-Algebra
data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord, Functor)
type Tree a = Fix (TreeF a)

instance (a ~ a') => FAlgebra (TreeF a) (Tree a') where
    algM = Iso runTransFix TransFix <$$> algM

{-
instance (a ~ a') => FAlgebra (TreeF a) (Tree a') where
    algM = Iso runNatFix NatFix <$$> algM
-}

empty :: forall a t. FAlgebra (TreeF a) t => t
empty = alg (Empty :: TreeF a t)

leaf :: forall a t. FAlgebra (TreeF a) t => a -> t
leaf a = alg $ Branch a e e
    where
    e = alg (Empty :: TreeF a t)

branch :: forall a t. FAlgebra (TreeF a) t => a -> t -> t -> t
branch a b1 b2 = alg $ Branch a b1 b2
