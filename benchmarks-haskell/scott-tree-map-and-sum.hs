{-# HLINT ignore "Use id" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Control.Monad.Fix (fix)

newtype ScottTree a = ScottTree (forall r. (a -> r) -> (ScottTree a -> ScottTree a -> r) -> r)

scottLeaf :: a -> ScottTree a
scottLeaf v = ScottTree (\leaf node -> leaf v)

scottNode :: ScottTree a -> ScottTree a -> ScottTree a
scottNode lhs rhs = ScottTree (\leaf node -> node lhs rhs)

scottTreeSum :: ScottTree Int -> Int
scottTreeSum = fix $ \rec tree ->
  case tree of
    ScottTree f ->
      f
        (\v -> v)
        (\lhs rhs -> rec lhs + rec rhs)

scottTreeMap :: (a -> b) -> ScottTree a -> ScottTree b
scottTreeMap = fix $ \rec f tree ->
  case tree of
    ScottTree g ->
      g
        (\v -> scottLeaf (f v))
        (\lhs rhs -> scottNode (rec f lhs) (rec f rhs))

generateTree :: Int -> ScottTree Int
generateTree = \case
  1 -> scottLeaf 1
  n -> scottNode (generateTree (n `div` 2)) (generateTree (n `div` 2))

benchmarkTerm :: Int
benchmarkTerm = scottTreeSum (scottTreeMap (* 2) (generateTree 16384))

main :: IO ()
main = print benchmarkTerm
