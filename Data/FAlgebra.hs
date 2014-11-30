{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.FAlgebra where

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Identity
import Control.Comonad
import Data.Bifunctor
import Data.Monoid

class FAlgebra f a | a -> f where
    alg :: f a -> a

class FCoalgebra f a | a -> f where
    coalg :: a -> f a

data Fix f = Fix { unFix :: f (Fix f) }
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)

instance FAlgebra f (Fix f) where
    alg = Fix

instance FCoalgebra f (Fix f) where
    coalg = unFix

newtype Wrapped f a = Wrap { unwrap :: f a }
    deriving (Eq, Show)

instance Functor f => Functor (Wrapped f) where
    fmap f = Wrap . fmap f . unwrap

instance (Functor f, FAlgebra f a) => FAlgebra f (Wrapped f a) where
    alg = Wrap . fmap alg . fmap unwrap

instance (Functor f, FCoalgebra f a) => FCoalgebra f (Wrapped f a) where
    coalg = fmap Wrap . fmap coalg . unwrap

instance (Functor f, FAlgebra f a) => FAlgebra f (Identity a) where
    alg = Identity . alg . fmap runIdentity

instance (Functor f, FCoalgebra f a) => FCoalgebra f (Identity a) where
    coalg = fmap Identity . coalg . runIdentity

instance (Functor f, FAlgebra f a1, FAlgebra f a2) => FAlgebra f (a1, a2) where
    alg as = (alg $ fmap fst as, alg $ fmap snd as)

instance (Functor f, FCoalgebra f a1, FCoalgebra f a2) => FCoalgebra f (Either a1 a2) where
    coalg (Left a1) = fmap Left (coalg a1)
    coalg (Right a2) = fmap Right (coalg a2)

newtype BFix f a = WrapBFix { unwrapBFix :: Fix (f a) }
deriving instance Eq (Fix (f a)) => Eq (BFix f a)
deriving instance Show (Fix (f a)) => Show (BFix f a)

instance Functor (f a) => FAlgebra (f a) (BFix f a) where
    alg = WrapBFix . Fix . fmap unwrapBFix

instance Functor (f a) => FCoalgebra (f a) (BFix f a) where
    coalg = fmap WrapBFix . unFix . unwrapBFix

instance Bifunctor f => Functor (BFix f) where
    fmap f (WrapBFix (Fix as)) = WrapBFix . Fix . bimap f (unwrapBFix . fmap f . WrapBFix) $ as

data FreeF f a r = Pure a | Free (f r)
    deriving (Eq, Show, Ord)
data CofreeF f a r = a :< (f r)
    deriving (Eq, Show, Ord)

instance Functor f => Bifunctor (FreeF f) where
    bimap f g (Pure a) = Pure (f a)
    bimap f g (Free as) = Free (fmap g as)

instance Functor f => Functor (FreeF f a) where
    fmap = second

instance Functor f => Bifunctor (CofreeF f) where
    bimap f g (a :< as) = f a :< fmap g as

instance Functor f => Functor (CofreeF f a) where
    fmap = second

-- WHYYYY ARE THERE SO MANY WRAPPERS
newtype Free f a = WrapFree { unwrapFree :: Fix (FreeF f a) }
deriving instance Show (Fix (FreeF f a)) => Show (Free f a)
newtype Cofree f a = WrapCofree { unwrapCofree :: Fix (CofreeF f a) }
deriving instance Show (Fix (CofreeF f a)) => Show (Cofree f a)

instance Functor f => FAlgebra (FreeF f a) (Free f a) where
    alg = WrapFree . alg . fmap unwrapFree
instance Functor f => FAlgebra (CofreeF f a) (Cofree f a) where
    alg = WrapCofree . alg . fmap unwrapCofree
instance Functor f => FCoalgebra (FreeF f a) (Free f a) where
    coalg = fmap WrapFree . coalg . unwrapFree
instance Functor f => FCoalgebra (CofreeF f a) (Cofree f a) where
    coalg = fmap WrapCofree . coalg . unwrapCofree

-- This could be derived from noting that FreeF is a bifunctor
instance Functor f => Functor (Free f) where
    fmap f (WrapFree (Fix (Pure a))) = WrapFree . Fix . Pure $ f a
    fmap f (WrapFree (Fix (Free as))) = WrapFree . Fix . Free $ fmap (unwrapFree . fmap f . WrapFree) as

instance Functor f => Monad (Free f) where
    return = WrapFree . Fix . Pure
    (WrapFree (Fix (Pure x))) >>= f = f x
    (WrapFree (Fix (Free xs))) >>= f = WrapFree . Fix . Free $ fmap (unwrapFree . (>>= f) . WrapFree) xs

instance Functor f => Applicative (Free f) where
    pure = return
    (<*>) = ap

instance Functor f => Functor (Cofree f) where
    fmap f (WrapCofree (Fix (a :< as))) = WrapCofree . Fix $ f a :< fmap (unwrapCofree . (fmap f) . WrapCofree) as

instance Functor f => Comonad (Cofree f) where
    extract (WrapCofree (Fix (a :< _))) = a
    extend f c@(WrapCofree (Fix (a :< as))) = WrapCofree . Fix $ f c :< fmap (unwrapCofree . extend f . WrapCofree) as

-- Goal: Have Ann f a be like Cofree f a but as an f-algebra
-- instead of a (CofreeF f a)-algebra.

-- Let's think about how the Ann algebra works
-- I'm combining two morphisms
-- f (AnnF f a r) -> f a -> a
-- f (AnnF f a r) -> f (f r) -> f r

-- Allows combining annotations without Compose
data AnnF a f r = AnnF a (f r)
    deriving (Eq, Show)
annFst (AnnF a _) = a
annSnd (AnnF _ as) = as

instance (Functor f) => Functor (AnnF a f) where
    fmap f (AnnF a as) = AnnF a (fmap f as)

-- Identity functor with a shadow type for the functor
-- in order to make fundeps work
newtype FIdentity (f :: * -> *) a = FIdentity { runFIdentity :: a }
    deriving (Eq, Show, Ord)

instance Functor (FIdentity f) where
    fmap f = FIdentity . f . runFIdentity

instance (Functor f, FAlgebra f a) => FAlgebra f (FIdentity f a) where
    alg = FIdentity . alg . fmap runFIdentity

instance (Functor f, FCoalgebra f a) => FCoalgebra f (FIdentity f a) where
    coalg = fmap FIdentity . coalg . runFIdentity

class FAlgebraFunctor f g | g -> f where
    algf :: forall r. FAlgebra f r => f (g r) -> g r

instance Functor f => FAlgebraFunctor f f where
    algf = fmap alg

-- This is the key!
-- We want
-- AnnF a (AnnF f b) r
-- To be an f-algebra (with appropriate conditions)
instance (Functor f, Functor f', FAlgebra f a, FAlgebraFunctor f f') => FAlgebraFunctor f (AnnF a f') where
    algf anns = AnnF (alg $ fmap annFst anns) (algf $ fmap annSnd anns)

-- TODO: Maybe better name?
data AnnFix f = AnnFix { unAnnFix :: f (AnnFix f) }
deriving instance Show (f (AnnFix f)) => Show (AnnFix f)

instance (Functor f, FAlgebraFunctor f g) => FAlgebra f (AnnFix g) where
    alg anns = AnnFix . algf $ fmap unAnnFix anns

newtype Ann f a = Ann { unAnn :: Cofree f a }
deriving instance Show (Cofree f a) => Show (Ann f a)
deriving instance Functor f => Functor (Ann f)

instance Functor f => Comonad (Ann f) where
    extract = extract . unAnn
    extend f = Ann . extend (f . Ann) . unAnn

instance (Functor f, FAlgebra f a) => FAlgebra f (Ann f a) where
    alg x = Ann . WrapCofree . Fix $ alg (fmap extract x) :< fmap (unwrapCofree . unAnn) x

instance Functor f => FCoalgebra f (Ann f a) where
    coalg (Ann (WrapCofree (Fix (_ :< as)))) = fmap (Ann . WrapCofree) as

-- Need newtype names for this
{-
instance Functor f => FAlgebra f (Free f a) where
    alg = WrapFree . Fix . Free . fmap unwrapFree

instance (Functor f, FCoalgebra f a) => FCoalgebra f (Free f a) where
    coalg (WrapFree (Fix (Pure x))) = fmap (WrapFree . Fix . Pure) $ coalg x
    coalg (WrapFree (Fix (Free xs))) = fmap WrapFree xs
-}

-- TODO: Foldable and Traversable instances where possible


-- Below this line is specific things for testing
data ListF a r = N | C a r deriving (Eq, Show, Ord, Functor)

instance Bifunctor ListF where
    bimap f g N = N
    bimap f g (C x y) = C (f x) (g y)

type List a = BFix ListF a

cons :: FAlgebra (ListF a) t => a -> t -> t
cons x xs = alg (C x xs)

nil :: List a
nil = WrapBFix (Fix N)

data Pair a = Pair a a deriving (Eq, Show, Ord, Functor)

data TreeF a b = Empty | Branch a b b deriving (Eq, Show, Ord, Functor)

instance Bifunctor TreeF where
    bimap f g Empty = Empty
    bimap f g (Branch a b1 b2) = Branch (f a) (g b1) (g b2)

type Tree a = BFix TreeF a

branch :: FAlgebra (TreeF a) t => a -> t -> t -> t
branch a b1 b2 = alg $ Branch a b1 b2

leaf :: FAlgebra (TreeF a) t => a -> t
leaf a = branch a empty empty

empty :: FAlgebra (TreeF a) t => t
empty = alg Empty

newtype Size a = Size Int deriving (Eq, Show, Ord, Num)

instance FAlgebra (TreeF a) (Size a) where
    alg Empty = 0
    alg (Branch _ b1 b2) = 1 + b1 + b2

type SizeTree a = Ann (TreeF a) (Size a)

newtype Combined a = Combined a deriving (Eq, Show, Ord, Num)

instance Monoid a => FAlgebra (TreeF a) (Combined a) where
    alg Empty = Combined mempty
    alg (Branch a (Combined b1) (Combined b2)) = Combined (b1 <> a <> b2)

type CombinedTree a = Ann (TreeF a) (Combined a)

type SizeAndCombinedTree a = Ann (TreeF a) (Size a, Combined a)

type SizeTree2 a = AnnFix (AnnF (Size a) (TreeF a))

type SizeAndCombinedTree2 a = AnnFix (AnnF (Combined a) (AnnF (Size a) (TreeF a)))

--TODO: Rewrite splay tree using this as 'smart constructors'
--(F-algebras are 'smart constructors', F-coalgebras are 'smart pattern matchers')
