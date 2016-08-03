--{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
--{-# LANGUAGE StandaloneDeriving #-}

{-
    Implementation of abstract machine semantics for Simon 
    Peyton-Jones's Delimited-Continuation Calculus (DCC). 
    All steps should be explicit to observe evolution of
    state through evaluation process.
-}

module DCC where

import Data.List

data ExprType = Redex | Value | Prompt | Empty
  deriving (Show, Eq)

data Expr = Var Char
          | Abs Char Expr
          | P Int
          | App Expr Expr
          | Sub Expr Expr Char
-- DCC additions
          | NewPrompt
          | PushPrompt Expr Expr
          | WithSubCont Expr Expr
          | PushSubCont Expr Expr
          
          | Hole
          | Compose [Expr]
          deriving (Show, Eq)

prettify :: Expr -> String
prettify (Var c) = [c]
prettify (Abs h m) = mconcat [ "(\\", [h], ".", prettify m, ")" ]
prettify (App m n) = mconcat [ prettify m, prettify n ]
prettify (Sub e1 e2 c) = mconcat [ prettify e1, "[", prettify e2, "/", [c], "]" ]
-- DANGER: i cannot be less than 11 ?!
prettify (P i) = show i
prettify NewPrompt = "newPrompt"
prettify (PushPrompt e1 e2) = mconcat ["pushPrompt", prettify e1, prettify e2]
prettify (WithSubCont e1 e2) = mconcat ["withSubCont", prettify e1, prettify e2]
prettify (PushSubCont e1 e2) = mconcat ["pushSubCont", prettify e1, prettify e2]
prettify Hole = "_"
prettify (Compose es) = foldr (++) "" $ intersperse ":" $ map prettify es

data State = State Expr Expr [Frame] Expr
  deriving (Show, Eq)
  
promptMatch :: Expr -> (Frame -> Bool)
promptMatch p = case p of
  P p -> \q -> case q of
    Tagged pair -> p == (fst pair)
    otherwise -> False
  otherwise -> \_ -> False

splitBefore :: [Frame] -> Expr -> [Frame]
splitBefore es p = takeWhile (not . promptMatch p) es

splitAfter :: [Frame] -> Expr -> [Frame]
splitAfter es p = case length list of
  0 -> []
  otherwise -> tail list
  where list = dropWhile (not . promptMatch p) es

extractFrame :: Frame -> Expr
extractFrame f = case f of
  Tagged p -> snd p
  Untagged e -> e

composeFrames :: [Frame] -> Expr
composeFrames es = Compose $ map extractFrame es

composeFrames' :: Expr -> [Frame] -> Expr
composeFrames' e es = case (composeFrames es) of (Compose es) -> Compose (e:es)
-- TODO: add Expr (n :: Ex | Val | Empty)

-- evaluation
eval :: State -> State
-- eval s = s

data Frame = Tagged (Int, Expr)
           | Untagged Expr
           deriving (Show, Eq)

---- searching for a redex
--
-- value of p implicitly indexes to position in stack
---- executing a redex
eval (State (App (Abs x e) v) d es q)  = State (Sub e v x) d es q
eval (State NewPrompt d es (P q)) = State (P q) d es (P $ q+1)
eval (State (PushPrompt (P i) e) d es q) = State e Hole (Tagged (i,d):es) q
eval (State (WithSubCont p v) d es q) = State (App v (composeFrames' d (splitBefore es p))) Hole (splitAfter es p) q
eval (State (PushSubCont e' e) d es q) = State e Hole (Untagged e':Untagged d:es) q

eval (State (Sub (Var m) y x) d es q) = State (if m == x then y else (Var m)) d es q
eval (State (Sub (App m n) y x) d es q) = State (App (Sub m y x) (Sub n y x)) d es q
eval (State (Sub (Abs h m) y x) d es q) = State (Abs h (Sub m y x)) d es q
eval (State (Sub (P p) y x) d es q) = State (P p) d es q
eval (State (Sub NewPrompt y x) d es q) = State NewPrompt d es q
eval (State (Sub (PushPrompt e1 e2) y x) d es q) = State (PushPrompt (Sub e1 y x) (Sub e2 y x)) d es q
eval (State (Sub (WithSubCont e1 e2) y x) d es q) = State (WithSubCont (Sub e1 y x) (Sub e2 y x)) d es q
eval (State (Sub (PushSubCont e1 e2) y x) d es q) = State (PushSubCont (Sub e1 y x) (Sub e2 y x)) d es q

-- TODO: this is unbelievably hacky
-- returning a value
eval (State (Var x) d es q) = evalVal $ State (Var x) d es q
eval (State (Abs x m) d es q) = evalVal $ State (Abs x m) d es q
eval (State (P p) d es q) = evalVal $ State (P p) d es q

eval (State v Hole [] q) = eval (State v Hole [] q)

evalVal :: State -> State
evalVal (State v d es q) = case d of
  Hole -> if length es == 0 
    then State v Hole es q
    else State v (extractFrame $ head es) (tail es) q
  otherwise -> State (App v d) Hole es q

prettifyState :: State -> String
prettifyState (State e d es q) = mconcat ["(", prettify e, ",", prettify d, if (length es) == 0 then ", [], " else ", E, ", prettify q, ")"]

evalFull s = do
  putStrLn $ (prettifyState s) ++ "\t" ++ (show s)
  let s' = eval s in
    if s == s'
      then putStrLn "terminated"
      else evalFull s'
