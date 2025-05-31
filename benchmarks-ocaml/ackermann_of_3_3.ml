open Interpreter

let is_zero = UnaryOp (fun x -> if x = 0 then 1 else 0)

let incr = UnaryOp (( + ) 1)

let decr = UnaryOp (fun x -> x - 1)

let ackermann =
  Fix
    (Lambda
       (Lambda
          (Lambda
             (IfThenElse
                ( Apply (is_zero, tvar 1),
                  Apply (incr, tvar 0),
                  IfThenElse
                    ( Apply (is_zero, tvar 0),
                      Apply (Apply (tvar 2, Apply (decr, tvar 1)), Const 1),
                      Apply
                        ( Apply (tvar 2, Apply (decr, tvar 1)),
                          Apply (Apply (tvar 2, tvar 1), Apply (decr, tvar 0))
                        ) ) )))))

let benchmark_term = Apply (Apply (ackermann, Const 3), Const 3)

let () =
  match denote [] benchmark_term with
  | VConst n -> Printf.printf "%d\n" n
  | _ -> failwith "Expected a constant result!"
