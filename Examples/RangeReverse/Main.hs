{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
import Prelude hiding (reverse, zip)
import qualified Prelude as P

import Control.Monad
import Control.Monad.Identity (Identity(..), runIdentity)

import Data.FAlgebra.Tree.Splay
import Data.Proxy

import System.CPUTime
import System.Random

import Lens.Micro

-- Expand a functor to incorporate a bit indicating whether the structure
-- should be reversed when traversing it.
data RevF f a = RevF !Bool (f a) deriving (Eq, Show, Ord, Functor)

newtype RevM a = RevM { runRevM :: a -> a }

reverse :: Structured RevM a => a -> a
reverse = runRevM struct

instance IsoRespecting RevM where
    liftIso (Iso to from) = Iso revTo revFrom
        where
        revTo (RevM r) = RevM (to . r . from)
        revFrom (RevM r) = RevM (from . r . to)

instance Preserving RevM (TreeF a) where
    trans (RevM r) = RevM $ \t -> case t of
        Empty -> Empty
        Branch a b1 b2 -> Branch a (r b2) (r b1)

instance (Structured RevM a, Preserving RevM f) => Preserving RevM (AnnF a f) where
    trans rev = RevM $ \(AnnF a xs) ->
        AnnF (reverse a) (runRevM (trans rev) xs)

instance Structured RevM (RevF f a) where
    struct = RevM $ \(RevF r xs) -> RevF (not r) xs

-- RevF "captures" the reverse operation
instance Preserving RevM (RevF f) where
    trans (RevM _) = RevM reverse

instance Natural f f' => Natural f (RevF f') where
    nat = RevF False . nat

instance RestrictedNatural s f f' => RestrictedNatural s f (RevF f') where
    rnat s = RevF False . rnat s

-- For size annotations, reversing does not change their value.
instance Structured RevM Size where
    struct = RevM id

-- Type of the trees we use to do efficient reversing
type RevSizeTreeF a = AnnF Size (RevF (TreeF a))
type RevSizeTree a = Fix (RevSizeTreeF a)

-- The type equality constraint here allows GHC to infer more types
-- at the cost of expressiveness that we don't need here.
instance (a ~ a') => FAlgebra (TreeF a) (RevSizeTree a') where
    alg = algRNat (Proxy :: Proxy (AnnM Size))

instance (a ~ a') => FCoalgebra (TreeF a) (RevSizeTree a') where
    coalg = coalgRNat (Proxy :: Proxy RevM)

instance (Preserving RevM f', RestrictedConatural RevM f f') => RestrictedConatural RevM f (RevF f') where
    rconat rev (RevF False as) = rconat rev as
    rconat rev (RevF True as) = rconat rev $ runRevM (trans rev) as

-- Allows us to use our general reverse on lists
instance Structured RevM [a] where
    struct = RevM P.reverse

-- Naive implementation of range reversals with list
-- Reverses the range [l, r) assuming l <= r
listReverseRange :: Int -> Int -> [a] -> [a]
listReverseRange l r as = as1 ++ reverse as2 ++ as3
    where
    as1 = take l as
    as2 = drop l (take r as)
    as3 = drop r as

treeReverseRange :: Int -> Int -> RevSizeTree a -> RevSizeTree a
treeReverseRange l r = zip . over _here reverse . isolateInterval l r

treeFromList :: forall a t. (FAlgebra (TreeF a) t, FCoalgebra (TreeF a) t, Structured (AnnM Size) t) => [a] -> t
treeFromList = foldr (insertAt 0) e
    where
    e = alg (Empty :: TreeF a t)

treeToList :: FCoalgebra (TreeF a) t => t -> [a]
treeToList t = case coalg t of
    Empty -> []
    Branch a b1 b2 -> treeToList b1 ++ [a] ++ treeToList b2

data TestCase = TestCase
    { size :: Int
    , reversals :: [(Int, Int)]
    } deriving (Eq, Show)

runTestCase :: (Int -> a) -> (Int -> Int -> a -> a) -> TestCase -> a
runTestCase init revRange (TestCase { size = s, reversals = revs }) = go (init s) revs
    where
    go = foldl (flip (uncurry revRange))

listRunTestCase = runTestCase (\n -> [0..(n-1)]) listReverseRange
treeRunTestCase = runTestCase (\n -> treeFromList [0..(n-1)]) treeReverseRange

sampleTestCase :: TestCase
sampleTestCase = TestCase
    { size = 10
    , reversals =
        [ (1, 5)
        , (5, 10)
        , (0, 10)
        ]
    }

randomIntervalIO :: Int -> IO (Int, Int)
randomIntervalIO size = do
    i <- randomRIO (0, size)
    j <- randomRIO (0, size)
    if i < j
        then return (i, j)
        else return (j, i)

randomTestCase :: Int -> Int -> IO TestCase
randomTestCase size nrevs = do
    revs <- replicateM nrevs (randomIntervalIO size)
    return TestCase
        { size = size
        , reversals = revs
        }

asSeconds :: Integer -> Double
asSeconds p = fromInteger p / 10^12

runComparison :: Int -> Int -> IO ()
runComparison size nrevs = do
    putStrLn $ show size ++ " " ++ show nrevs
    testcase <- randomTestCase size nrevs
    -- print testcase
    listStart <- getCPUTime
    let listResult = listRunTestCase testcase
    -- Force entire list
    -- print listResult
    length listResult `seq` return ()
    listEnd <- getCPUTime
    print . asSeconds $ listEnd - listStart
    treeStart <- getCPUTime
    let treeResult = treeToList (treeRunTestCase testcase)
    -- print treeResult
    length treeResult `seq` return ()
    treeEnd <- getCPUTime
    print . asSeconds $ treeEnd - treeStart
    print $ listResult == treeResult

main :: IO ()
main = do
    runComparison 1000 1000
    runComparison 2000 2000
    runComparison 4000 4000
    runComparison 8000 8000
    runComparison 16000 16000
    -- runComparison 32000 32000
