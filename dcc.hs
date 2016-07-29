{-
    Implementation of abstract machine semantics for Simon 
    Peyton-Jones's Delimited-Continuation Calculus (DCC). 
    All steps should be explicit to observe evolution of
    state through evaluation process.
-}

module DCC where

data Expr = Var Char
          | P Int
          | Abs Char Expr
          | App Expr Expr
          | Sub Expr Expr Char
          | NewPrompt
          | PushPrompt Int Expr
          deriving (Show, Eq)
        
data State = State Expr Int [(Int, Expr)]
  deriving (Show, Eq)

showExpr :: Expr -> String
showExpr (Var x) = [x]
showExpr (Abs h b) = "(\\" ++ [h] ++ "." ++ (showExpr b) ++ ")"
showExpr (App m n) = showExpr m ++ (showExpr n)
showExpr (Sub e1 e2 c) = showExpr e1 ++ "[" ++ (showExpr e2) ++ "/" ++ [c] ++ "]"

showExpr (NewPrompt) = "newPrompt"
showExpr (PushPrompt p exp) = "pushPrompt " ++ (show p) ++ (show exp)
showExpr  (P i) = "p(" ++ (show i) ++ ")"

showState :: State -> String
showState (State expr q e) = "(" ++ (showExpr expr) ++ ", " ++ (show q) ++ ", " ++ (show e) ++ ")"

eval :: State -> State
eval (State (Var a) q e)            = (State (Var a) q e)
eval (State NewPrompt q e)          = (State (P q) (q+1) e)
eval (State (PushPrompt p ex) q  e) = (State ex q ((p, ex):e))

testExpr expr = showState $ eval (State expr 0 [])
test expr = showState $ eval expr
