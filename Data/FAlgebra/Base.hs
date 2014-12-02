{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra.Base where

class FAlgebra f a | a -> f where
    alg :: f a -> a

class FCoalgebra f a | a -> f where
    coalg :: a -> f a

class FCoalgebraFixable f g | g -> f where
    coalgfix :: forall r. FCoalgebra f r => (r -> g r) -> g r -> f (g r)

class FAlgebraTrans f g | g -> f where
    algf :: forall r. FAlgebra f r => f (g r) -> g r

class FCoalgebraFixable f g => FCoalgebraTrans f g | g -> f where
    coalgf :: forall r. FCoalgebra f r => g r -> f (g r)

instance Functor f => FAlgebraTrans f f where
    algf = fmap alg

instance Functor f => FCoalgebraTrans f f where
    coalgf = fmap coalg

class FCoalgebraFixable f g => FCoalgebraNatural f g | g -> f where
    nat :: forall r. g r -> f r

instance Functor f => FCoalgebraNatural f f where
    nat = id

-- Default implementations of coalgfix for the two subclasses
coalgfixTrans :: (FCoalgebraTrans f g, FCoalgebra f r) => (r -> g r) -> g r -> f (g r)
coalgfixTrans = const coalgf

coalgfixNat :: (Functor f, FCoalgebraNatural f g) => (r -> g r) -> g r -> f (g r)
coalgfixNat unfix = fmap unfix . nat

instance Functor f => FCoalgebraFixable f f where
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
