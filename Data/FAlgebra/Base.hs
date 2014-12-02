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

-- This is going to be a bit sad without defaults for
-- superclasses.
-- This is a class of functors g such that Fix g is
-- a f-algebra.
class FAlgebraFixable f g | g -> f where
    algfix :: forall r. FAlgebra f r => (g r -> r) -> (r -> g r) -> f (g r) -> g r

class FCoalgebraFixable f g | g -> f where
    coalgfix :: forall r. FCoalgebra f r => (g r -> r) -> (r -> g r) -> g r -> f (g r)

class FAlgebraFixable f g => FAlgebraTrans f g | g -> f where
    algf :: forall r. FAlgebra f r => f (g r) -> g r

class FCoalgebraFixable f g => FCoalgebraTrans f g | g -> f where
    coalgf :: forall r. FCoalgebra f r => g r -> f (g r)

-- Defaults for algfix and coalgfix
-- Which you can use 
algfixDefault :: (FAlgebra f r, FAlgebraTrans f g) => (g r -> r) -> (r -> g r) -> f (g r) -> g r
algfixDefault _ _ = algf

coalgfixDefault :: (FCoalgebra f r, FCoalgebraTrans f g) => (g r -> r) -> (r -> g r) -> g r -> f (g r)
coalgfixDefault _ _ = coalgf

instance Functor f => FAlgebraTrans f f where
    algf = fmap alg

instance Functor f => FAlgebraFixable f f where
    algfix = algfixDefault

instance Functor f => FCoalgebraTrans f f where
    coalgf = fmap coalg

instance Functor f => FCoalgebraFixable f f where
    coalgfix = coalgfixDefault

newtype Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

-- f (Fix g) -> f (g (Fix g)) -> g (Fix g) -> Fix g
instance (Functor f, FAlgebraFixable f g) => FAlgebra f (Fix g) where
    alg = Fix . algfix Fix unFix . fmap unFix

-- Fix g -> g (Fix g) -> f (g (Fix g)) -> f (Fix g)
instance (Functor f, FCoalgebraFixable f g) => FCoalgebra f (Fix g) where
    coalg = fmap Fix . coalgfix Fix unFix . unFix

