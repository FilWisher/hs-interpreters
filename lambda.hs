{-

  Lazy lambda-calculus interpreter for showing step-by-step
  evaluation of lambda-terms.

-}

module Lambda where

data Expr = Var Char
          | Abs Char Expr
          | App Expr Expr
          | Sub Expr Expr Char
          deriving (Show, Eq)

stringify :: Expr -> String
stringify (Var x) = [x]
stringify (Abs h b) = "(\\" ++ [h] ++ "." ++ (stringify b) ++ ")"
stringify (App m n) = stringify m ++ (stringify n)
stringify (Sub e1 e2 c) = stringify e1 ++ "[" ++ (stringify e2) ++ "/" ++ [c] ++ "]"

eval :: Expr -> Expr
eval (Var x) = (Var x)
eval (App m n) = case (eval m) of
  (Abs x e) -> Sub e (eval n) x
  e         -> App m (eval n)
eval (Abs h b) = (Abs h b)
eval (Sub e1 e2 c) = case (eval e1) of
  (Var a)     -> if a == c then (eval e2) else (Var a)
  (App e3 e4) -> App (Sub e3 e2 c) (Sub e4 e2 c)
  (Abs h b)   -> Abs h (Sub b e2 c)

evalFull x = do
  putStrLn $ (stringify x) ++ "\t"  ++ (show x)
  let y = eval x in 
    if x == y
      then putStrLn "terminated"
      else evalFull y
