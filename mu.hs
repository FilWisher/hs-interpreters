{-

  Lazy lambda-mu calculus interpreter for showing step-by-step
  evaluation of lambda-mu terms. Following Steffen van Bakel's
  interpretation of Parigot's original calculus.

-}

module Mu where

type LVar = Char
type MVar = Char

data Named = Named MVar Expr
  deriving (Show, Eq)

data Expr = Var LVar
  | Abs LVar Expr 
  | App Expr Expr
  --    m   [ x  /  y ]
  | Sub Expr Expr LVar
  | MSub Expr Expr MVar
  | Mu MVar Named
  deriving (Show, Eq)
  

stringExpr :: Expr -> String
stringExpr (Var x) = [x]
stringExpr (Abs h b) = mconcat ["(\\", [h], ".", stringExpr b, ")"]
stringExpr (App m n) = mconcat [stringExpr m, stringExpr n]
stringExpr (Sub e1 e2 c) = mconcat [stringExpr e1, "[", stringExpr e2, "/", [c], "]"]
stringExpr (Msub e1 e2 a) = mconcat [stringExpr e1, "[ [", [a], "]m'", stringExpr e2, "/[", [a], "]m' ]"]
stringExpr (Mu n nex) = mconcat ["m", [n], ".", stringNamed nex]

stringNamed :: Named -> String
stringNamed (Named n ex) = mconcat ["[", [n], "]", stringExpr ex]

-- TODO: define app for msubs

eval :: Expr -> Expr
eval (Var x) = (Var x)

eval (App (Abs x m) n) = Sub m n x
eval (App (Mu alpha (Named beta m)) n) = Mu alpha (Named beta (MSub m n alpha))

eval (Sub (Var m) y x) = if m == x then y else (Var m)
eval (Sub (App m n) y x) = App (Sub m y x) (Sub n y x)
eval (Sub (Abs h m) y x) = Abs h (Sub m y x)
eval (Sub (Mu alpha (Named beta m)) y x) = Mu alpha (Named beta (Sub m y x))

eval (MSub (Var m) _ _) = (Var m)
eval (MSub (Abs x m) n alpha) = Abs x (MSub m n alpha)
eval (MSub (App x y) n alpha) = App (MSub x n alpha) (MSub y n alpha)
eval (MSub (Mu delta (Named alpha m)) n gamma) = 
  if gamma == alpha
    then Mu delta (Named alpha (App (MSub m n alpha) n))
    else Mu delta (Named alpha (MSub m n alpha))

evalFull x = do
  putStrLn $ (stringExpr x) ++ "\t"  ++ (show x)
  let y = eval x in 
    if x == y
      then putStrLn "terminated"
      else evalFull y
