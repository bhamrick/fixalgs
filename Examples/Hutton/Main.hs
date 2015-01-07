{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Data.FAlgebra

import Data.Proxy

-- Implementation of the following article with F-Algebras instead of pattern synonyms
-- http://mpickering.github.io/posts/2014-11-27-pain-free.html

data HuttonF a = Int Int | Add a a
    deriving (Eq, Show, Functor)

type Hutton = Fix HuttonF

instance FAlgebra HuttonF Int where
    alg (Int x) = x
    alg (Add x y) = x + y

eval :: FCoalgebra HuttonF a => a -> Int
eval = hylo (Proxy :: Proxy HuttonF)

int :: FAlgebra HuttonF a => Int -> a
int x = alg (Int x)

add :: FAlgebra HuttonF a => a -> a -> a
add x y = alg (Add x y)

p1 :: FAlgebra HuttonF a => a
p1 = add (int 5) (int 6)

p2 :: Hutton
p2 = p1

-- Annotate each expression with the number of summands
instance FAlgebra HuttonF Size where
    alg (Int _) = 1
    alg (Add x y) = x + y

type SizedHuttonF = AnnF Size HuttonF
type SizedHutton = Fix SizedHuttonF

p3 :: SizedHutton
p3 = p1

instance FAlgebra HuttonF SizedHutton where
    alg = algRNat (Proxy :: Proxy (AnnM Size))

instance FCoalgebra HuttonF SizedHutton where
    coalg = coalgNat

type HoleHuttonF = HoleF () HuttonF
type HoleHutton = Fix HoleHuttonF

instance FAlgebra HuttonF HoleHutton where
    alg = algNat

hole :: forall a. FAlgebra HoleHuttonF a => a
hole = alg (Hole () :: HoleHuttonF a)

p4 :: HoleHutton
p4 = add (int 5) hole

fillHole :: (() -> Hutton) -> HoleHutton -> Hutton
fillHole f hh = case (coalg hh :: HoleHuttonF HoleHutton) of
    Hole a -> f a
    Full v -> alg (fmap (fillHole f) v)

main :: IO ()
main = do
    print p2
    print $ eval p2
    print p3
    print $ eval p3
    print p4
    print $ fillHole (const p2) p4
    print . eval $ fillHole (const p2) p4
