import Control.Monad.Fix (fix)

ackermann :: Int -> Int -> Int
ackermann =
  fix
    ( \rec m n ->
        if m == 0
          then n + 1
          else
            if n == 0
              then rec (m - 1) 1
              else rec (m - 1) (rec m (n - 1))
    )

main :: IO ()
main = print (ackermann 3 3)
