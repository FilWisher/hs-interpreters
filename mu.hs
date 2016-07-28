{-

  Lazy lambda-mu calculus interpreter for showing step-by-step
  evaluation of lambda-mu terms

-}

module Mu where

data NExp = NExp Char Expr
  deriving (Show, Eq)

data Expr = Var Char
          | Abs Char Expr
          | App Expr Expr
          | Sub Expr Expr Char
          | Mu Char NExp
          deriving (Show, Eq)

stringify :: Expr -> String
stringify (Var x) = [x]
stringify (Abs h b) = mconcat ["(\\", [h], ".", stringify b, ")"]
stringify (App m n) = mconcat [stringify m, stringify n]
stringify (Sub e1 e2 c) = mconcat [stringify e1, "[", stringify e2, "/", [c], "]"]

stringify (Mu v exp) = case exp of
  (NExp a exp') -> mconcat ["m", [v], ".[", [a], "]", (stringify exp')]

test = stringify $ Mu 'a' (NExp 'a' (Var 'x'))

eval = flip evalMap []

-- TODO: write tests for lamda-mu terms
-- TODO: complete rewrite rules of (Sub ...)
-- TODO: does mu application skip explicit substitution step?
evalMap :: Expr -> [(Char, Expr)] -> Expr
evalMap (Var x) es   = (Var x)
evalMap (App m n) es = case (eval m) of
  (Abs x e) -> Sub e (evalMap n es) x
  (Mu v nexp) -> case nexp of 
      (NExp l exp) -> Mu v $ evalNamed (NExp l $ evalMap exp ((v, n):es)) ((v, n):es)
  e -> App m (evalMap n es)
evalMap (Abs h b) es = (Abs h b)
evalMap (Mu c nexp) es = case nexp of
  (NExp _ (Var x)) -> Var x 
  otherwise        -> (Mu c nexp)
--eval (Sub e1 e2 c) = case (eval e1) of
--  (Var a)     -> if a == c then (eval e2) else (Var a)
--  (App e3 e4) -> App (Sub e3 e2 c) (Sub e4 e2 c)
--  (Abs h b)   -> Abs h (Sub b e2 c)

--evalNamed :: NExp -> [(Char, Expr)] -> NExp
evalNamed (NExp n exp) es =
  if len == 0
    then (NExp n exp)
    else (NExp n $ loop exp list)
  where list = map snd $ filter (\(x, y) -> (n==x)) es
        len  = length list
        loop e [] = e
        loop e l =
          loop (App e $ head l) (tail l)

-- evalMap ((Mu v exp), es) = evalMap
  

--evalFull x = do
--  putStrLn $ (stringify x) ++ "\t"  ++ (show x)
--  let y = eval x in 
--    if x == y
--      then putStrLn "terminated"
--      else evalFull y
