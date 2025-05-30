import Interpreter

isZero :: Term
isZero = UnaryOp (\x -> if x == 0 then 1 else 0)

incr :: Term
incr = UnaryOp (+ 1)

decr :: Term
decr = UnaryOp (\x -> x - 1)

ackermann :: Term
ackermann =
  Fix
    ( Lambda
        ( Lambda
            ( Lambda
                ( IfThenElse
                    (Apply isZero (TVar 1))
                    (Apply incr (TVar 0))
                    ( IfThenElse
                        (Apply isZero (TVar 0))
                        (Apply (Apply (TVar 2) (Apply decr (TVar 1))) (Const 1))
                        ( Apply
                            (Apply (TVar 2) (Apply decr (TVar 1)))
                            (Apply (Apply (TVar 2) (TVar 1)) (Apply decr (TVar 0)))
                        )
                    )
                )
            )
        )
    )

benchmarkTerm :: Term
benchmarkTerm = Apply (Apply ackermann (Const 3)) (Const 3)

main :: IO ()
main = case denote [] benchmarkTerm of
  VConst n -> print n
  _ -> error "Expected a constant result!"
