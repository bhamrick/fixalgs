{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
import Data.FAlgebra.Annotation
import Data.FAlgebra.Base

import Data.Foldable
import Data.Traversable
import Data.Monoid

-- Based on http://brianmckenna.org/blog/type_annotation_cofree
data ASTF a = ALambda String a
            | AApply a a
            | ANumber Int
            | AString String
            | AIdent String

type AST = Fix ASTF

instance FAlgebra ASTF AST where
    alg = Fix

instance FCoalgebra ASTF AST where
    coalg = unFix

deriving instance Show a => Show (ASTF a)
deriving instance Functor ASTF
deriving instance Foldable ASTF
deriving instance Traversable ASTF
deriving instance Eq a => Eq (ASTF a)
deriving instance Ord a => Ord (ASTF a)

lambda :: FAlgebra ASTF a => String -> a -> a
lambda v e = alg (ALambda v e)

apply :: FAlgebra ASTF a => a -> a -> a
apply e1 e2 = alg (AApply e1 e2)

number :: FAlgebra ASTF a => Int -> a
number n = alg (ANumber n)

string :: FAlgebra ASTF a => String -> a
string s = alg (AString s)

ident :: FAlgebra ASTF a => String -> a
ident v = alg (AIdent v)

example :: FAlgebra ASTF a => a
example = apply (lambda "x" $ ident "x") (number 2)

data Type = TLambda Type Type
          | TVar Int
          | TNumber
          | TString

deriving instance Show Type

data Constraint = EqualityConstraint Type Type

deriving instance Show Constraint

data TypeResult = TypeResult
    { constraints :: [Constraint]
    , assumptions :: M.Map String [Type]
    }

deriving instance Show TypeResult

instance Monoid TypeResult where
    mempty = TypeResult
        { constraints = mempty
        , assumptions = mempty
        }
    mappend a b = TypeResult
        { constraints = constraints a `mappend` constraints b
        , assumptions = assumptions a `mappend` assumptions b
        }

data TypeState t m = TypeState
    { varId :: Int
    , memo :: M.map t m
    }


