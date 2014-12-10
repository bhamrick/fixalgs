{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Prelude hiding (reverse, zip)
import qualified Prelude as P

import Control.Monad

import Data.FAlgebra.Annotation
import Data.FAlgebra.Base
import Data.FAlgebra.Tree
import Data.FAlgebra.TreeZipper

import System.CPUTime
import System.Random

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
treeReverseRange l r = zip . local reverse . isolateInterval l r

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
    }

runTestCase :: (Int -> a) -> (Int -> Int -> a -> a) -> TestCase -> a
runTestCase init revRange (TestCase { size = s, reversals = revs }) = go (init s) revs
    where
    go acc [] = acc
    go acc (r:rs) = go (uncurry revRange r acc) rs

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
    return $ TestCase
        { size = size
        , reversals = revs
        }

asSeconds :: Integer -> Double
asSeconds p = fromInteger p / 10^12

runComparison :: Int -> Int -> IO ()
runComparison size nrevs = do
    putStrLn $ show size ++ " " ++ show nrevs
    testcase <- randomTestCase size nrevs
    listStart <- getCPUTime
    length (listRunTestCase testcase) `seq` return ()
    listEnd <- getCPUTime
    print . asSeconds $ listEnd - listStart
    treeStart <- getCPUTime
    length (treeToList (treeRunTestCase testcase)) `seq` return ()
    treeEnd <- getCPUTime
    print . asSeconds $ treeEnd - treeStart

main :: IO ()
main = do
    runComparison 1000 1000
    runComparison 2000 2000
    runComparison 4000 4000
    runComparison 8000 8000
    runComparison 16000 16000
    runComparison 32000 32000
