{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
-- TypeFamilies is currently only used for equality constraints
-- It's possible it should be used everywhere, though.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Base where

-- TODO: Learn about type families and see if they are a better fit

class FAlgebra f a | a -> f where
    alg :: f a -> a

class FCoalgebra f a | a -> f where
    coalg :: a -> f a

instance (Functor f, FAlgebra f a1, FAlgebra f a2) => FAlgebra f (a1, a2) where
    alg as = (alg (fmap fst as), alg (fmap snd as))

instance (Functor f, FCoalgebra f a1, FCoalgebra f a2) => FCoalgebra f (Either a1 a2) where
    coalg (Left a) = fmap Left (coalg a)
    coalg (Right a) = fmap Right (coalg a)

class FAlgebraFixable f g | g -> f where
    algfix :: forall r. FAlgebra f r => (g r -> r) -> f (g r) -> g r

class FCoalgebraFixable f g | g -> f where
    coalgfix :: forall r. FCoalgebra f r => (r -> g r) -> g r -> f (g r)

class FAlgebraFixable f g => FAlgebraTrans f g | g -> f where
    algf :: forall r. FAlgebra f r => f (g r) -> g r

class FCoalgebraFixable f g => FCoalgebraTrans f g | g -> f where
    coalgf :: forall r. FCoalgebra f r => g r -> f (g r)

-- We use OverlappingInstances and TypeFamilies here so that
-- these instances are the most general when considering
-- only the instance head, so they will be considered last,
-- which allows GHC to figure out which type we want in some
-- additional circumstances.
instance (Functor f, f ~ f') => FAlgebraTrans f f' where
    algf = fmap alg

instance (Functor f, f ~ f') => FCoalgebraTrans f f' where
    coalgf = fmap coalg

class FAlgebraFixable f g => FAlgebraNatural f g | g -> f where
    nat :: forall r. f r -> g r

class FCoalgebraFixable f g => FCoalgebraNatural f g | g -> f where
    conat :: forall r. g r -> f r

instance (Functor f, f ~ f') => FAlgebraNatural f f' where
    nat = id

instance (Functor f, f ~ f') => FCoalgebraNatural f f' where
    conat = id

-- Default implementations of algfix for the two subclasses
algfixTrans :: (FAlgebraTrans f g, FAlgebra f r) => (g r -> r) -> f (g r) -> g r
algfixTrans = const algf

algfixNat :: (Functor f, FAlgebraNatural f g) => (g r -> r) -> f (g r) -> g r
algfixNat fix = nat . fmap fix

-- Default implementations of coalgfix for the two subclasses
coalgfixTrans :: (FCoalgebraTrans f g, FCoalgebra f r) => (r -> g r) -> g r -> f (g r)
coalgfixTrans = const coalgf

coalgfixNat :: (Functor f, FCoalgebraNatural f g) => (r -> g r) -> g r -> f (g r)
coalgfixNat unfix = fmap unfix . conat

instance (Functor f, f ~ f') => FAlgebraFixable f f' where
    algfix = algfixNat

instance (Functor f, f ~ f') => FCoalgebraFixable f f' where
    coalgfix = coalgfixNat

newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

-- f (Fix g) -> f (g (Fix g)) -> g (Fix g) -> Fix g
instance (Functor f, FAlgebraTrans f g) => FAlgebra f (Fix g) where
    alg = Fix . algf . fmap unFix

{-
-- Fix g -> g (Fix g) -> f (g (Fix g)) -> f (Fix g)
instance (Functor f, FCoalgebraTrans f g) => FCoalgebra f (Fix g) where
    coalg = fmap Fix . coalgf . unFix
-}

instance (Functor f, FCoalgebraFixable f g) => FCoalgebra f (Fix g) where
    coalg = fmap Fix . coalgfix unFix . unFix
