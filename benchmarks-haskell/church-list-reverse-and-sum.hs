{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant lambda" #-}

import Control.Monad.Fix (fix)

churchNil = \f n -> n

churchCons = \h t f n -> f h (t f n)

churchSumList = \list -> list (+) 0

churchReverse = \xs -> xs (\x cont f n -> cont f (f x n)) churchNil

generateList n = go n churchNil
  where
    go 0 acc = acc
    go i acc = go (i - 1) (churchCons (i - 1) acc)

benchmarkTerm :: Int
benchmarkTerm = churchSumList (churchReverse (generateList 3000))

main :: IO ()
main = print benchmarkTerm
