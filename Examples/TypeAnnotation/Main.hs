{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
import Prelude hiding (sequence, foldl)

import Control.Applicative
import Control.Monad.State hiding (sequence)

import Data.FAlgebra.Annotation
import Data.FAlgebra.Base

import Data.Foldable
import Data.Traversable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid

import Lens.Micro

-- Based on http://brianmckenna.org/blog/type_annotation_cofree
data ASTF a = ALambda String a
            | AApply a a
            | ANumber Int
            | AString String
            | AIdent String

type AST = Fix ASTF

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
    , assumptions :: Map String [Type]
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

newtype VarIdSource = VarIdSource Int
    deriving (Eq, Show, Ord)

freshVarId :: MonadState VarIdSource m => m Type
freshVarId = do
    VarIdSource varId <- get
    modify $ \(VarIdSource i) -> VarIdSource (i+1)
    return $ TVar varId

generateConstraintStep :: MonadState VarIdSource m => ASTF (Type, TypeResult) -> m (Type, TypeResult)
generateConstraintStep (ANumber _) = return (TNumber, mempty)
generateConstraintStep (AString _) = return (TString, mempty)
generateConstraintStep (AIdent s) = do
    var <- freshVarId
    return (var, TypeResult {
        constraints = [],
        assumptions = Map.singleton s [var]
        })
generateConstraintStep (ALambda s (b_type, b_type_res)) = do
    var <- freshVarId
    let cs = maybe [] (map $ EqualityConstraint var) (Map.lookup s . assumptions $ b_type_res)
        as = Map.delete s (assumptions b_type_res)
    return (TLambda var b_type, TypeResult {
        constraints = constraints b_type_res `mappend` cs,
        assumptions = as
        })
generateConstraintStep (AApply (a_type, a_type_res) (b_type, b_type_res)) = do
    var <- freshVarId
    return (var, a_type_res `mappend` b_type_res `mappend` TypeResult {
        constraints = [EqualityConstraint a_type $ TLambda b_type var],
        assumptions = mempty
        })

-- This is a semisequence
generateConstraintSemisequence :: (Structured (AnnM (Type, TypeResult)) b, MonadState VarIdSource m) => ASTF (m b) -> m (AnnF (Type, TypeResult) ASTF b)
generateConstraintSemisequence ast = do
    ast' <- sequence ast
    let annotations = fmap getAnnotation ast'
    topAnnotation <- generateConstraintStep annotations
    return (AnnF topAnnotation ast')

type ConstraintAST = Fix (AnnF (Type, TypeResult) ASTF)

generateConstraints :: AST -> ConstraintAST
generateConstraints = flip evalState (VarIdSource 0) . sequenceFix generateConstraintSemisequence

solveConstraints :: [Constraint] -> Maybe (Map Int Type)
solveConstraints =
    foldl (\b a -> liftM2 mappend (solve b a) b) $ Just Map.empty
        where
        solve maybeSubs (EqualityConstraint a b) = do
            subs <- maybeSubs
            mostGeneralUnifier (substitute subs a) (substitute subs b)

mostGeneralUnifier :: Type -> Type -> Maybe (Map Int Type)
mostGeneralUnifier (TVar i) b = Just $ Map.singleton i b
mostGeneralUnifier a (TVar i) = Just $ Map.singleton i a
mostGeneralUnifier TNumber TNumber = Just Map.empty
mostGeneralUnifier TString TString = Just Map.empty
mostGeneralUnifier (TLambda a b) (TLambda c d) = do
    s1 <- mostGeneralUnifier a c
    mappend <$> mostGeneralUnifier (substitute s1 b) (substitute s1 d) <*> Just s1
mostGeneralUnifier _ _ = Nothing

substitute :: Map Int Type -> Type -> Type
substitute subs v@(TVar i) = maybe v (substitute subs) $ Map.lookup i subs
substitute subs (TLambda a b) = TLambda (substitute subs a) (substitute subs b)
substitute _ t = t

type TypedAST = Fix (AnnF Type ASTF)

solveConstraintTree :: ConstraintAST -> Maybe TypedAST
solveConstraintTree ast = do
    let (ast_type, ast_type_res) = getAnnotation ast :: (Type, TypeResult)
    subs <- solveConstraints (constraints ast_type_res)
    return $ fmapFix (over _ann (substitute subs . fst)) ast

typeTree :: AST -> Maybe TypedAST
typeTree = solveConstraintTree . generateConstraints

main :: IO ()
main = do
    print (example :: AST)
    print $ generateConstraints example
    print $ typeTree example
