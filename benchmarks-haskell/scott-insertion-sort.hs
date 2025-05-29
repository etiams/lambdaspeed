{-# HLINT ignore "Use const" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Control.Monad.Fix (fix)

newtype ScottList a = ScottList (forall r. r -> (a -> ScottList a -> r) -> r)

scottNil :: ScottList a
scottNil = ScottList (\n c -> n)

scottCons :: a -> ScottList a -> ScottList a
scottCons h t = ScottList (\n c -> c h t)

scottSingleton :: a -> ScottList a
scottSingleton x = scottCons x scottNil

scottInsertionSort :: ScottList Int -> ScottList Int
scottInsertionSort =
  fix $ \rec (ScottList f) -> f scottNil (\x xs -> scottInsert x (rec xs))

scottInsert :: Int -> ScottList Int -> ScottList Int
scottInsert = fix $ \rec y (ScottList f) ->
  f
    (scottSingleton y)
    ( \z zs ->
        if y <= z
          then scottCons y (scottCons z zs)
          else scottCons z (rec y zs)
    )

scottConcatenateList :: ScottList Int -> Int
scottConcatenateList =
  fix $ \rec (ScottList f) -> f 0 (\x xs -> concatenateInts (fromIntegral x) (rec xs))

concatenateInts :: Int -> Int -> Int
concatenateInts x y =
  let countDigits = \case
        0 -> 1
        n -> if n < 10 then 1 else 1 + countDigits (n `div` 10)
   in x * (10 ^ countDigits y) + y

generateList :: Int -> ScottList Int
generateList n = go n scottNil
  where
    go 0 acc = acc
    go i acc = go (i - 1) (scottCons (i - 1) acc)

benchmarkTerm :: Int
benchmarkTerm =
  scottConcatenateList (scottInsertionSort (generateList 100))

main :: IO ()
main = print benchmarkTerm
