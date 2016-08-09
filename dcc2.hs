--{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
--{-# LANGUAGE StandaloneDeriving #-}

module DCC where 

import Data.List

data Expr = Var Char
  | Abs Char Expr
  | App Expr Expr
  | Prompt Int
  | Hole
  | PushPrompt Expr Expr
  | PushSubCont Expr Expr
  | WithSubCont Expr Expr
  | NewPrompt
  | Seq [Expr]
  
  | Return Expr Expr
  | Sub Expr Expr Char
  deriving (Show, Eq)

prettify :: Expr -> String
prettify (Var c) = [c]
prettify (Abs h m) = mconcat [ "(\\", [h], ".", prettify m, ")" ]
prettify (App m n) = mconcat [ prettify m, prettify n ]
prettify (Prompt i) = show i
prettify NewPrompt = "newPrompt"
prettify (PushPrompt e1 e2) = mconcat ["pushPrompt", prettify e1, prettify e2]
prettify (WithSubCont e1 e2) = mconcat ["withSubCont", prettify e1, prettify e2]
prettify (PushSubCont e1 e2) = mconcat ["pushSubCont", prettify e1, prettify e2]
prettify Hole = "_"
prettify (Seq es) = foldr (++) "" $ intersperse ":" $ map prettify es

prettify (Sub e1 e2 c) = mconcat [ prettify e1, "[", prettify e2, "/", [c], "]" ]
prettify (Return d v) = prettify filled
  where filled = case d of
          Hole -> v
          (App Hole e) -> App v e
          (App e Hole) -> App e v
          PushPrompt Hole e -> PushPrompt v e
          WithSubCont Hole e -> WithSubCont v e
          WithSubCont e Hole -> WithSubCont e v
          PushSubCont Hole e -> PushSubCont v e

prettifyState :: State -> String
prettifyState (State e d es q) = mconcat ["(", prettify e, ", ", prettify d, if (length es) == 0 then ", [], " else ", E, ", prettify q, ")"]

data State = State Expr Expr [Expr] Expr
  deriving (Show, Eq)

isValue :: Expr -> Bool
isValue e = case e of
  Var _ -> True
  Prompt _ -> True
  Abs _ _ -> True
  Seq _ -> True
  otherwise -> False

eval :: State -> State
eval (State (App e e') d es q) = 
  if isValue e then 
    State e' (Return d (App e Hole)) es q
  else
    State e (Return d (App Hole e')) es q

eval (State (PushPrompt e e') d es q) =
  if isValue e then
    State e' Hole (e:d:es) q
  else
    State e (Return d (PushPrompt Hole e')) es q

eval (State (WithSubCont e e') d es q) =
  if isValue e then
    if isValue e' then
      case e of (Prompt p) -> State (App e' (Seq (d:(splitBefore p es)))) Hole (splitAfter p es) q
    else
      State e' (Return d (WithSubCont e Hole)) es q
  else
    State e (Return d (WithSubCont Hole e')) es q
    
eval (State (PushSubCont e e') d es q) =
  if isValue e then
    case e of (Seq s) -> State e Hole (s++(d:es)) q
  else
    State e (Return d (PushSubCont Hole e')) es q
    
eval (State (App (Abs x e) v) d es q) = State (Sub e v x) d es q

eval (State (Sub (Var m) v x) d es q) = State (if m == x then v else (Var m)) d es q
eval (State (Sub (App m n) y x) d es q) = State (App (Sub m y x) (Sub n y x)) d es q
eval (State (Sub (Abs h m) y x) d es q) = State (Abs h (Sub m y x)) d es q
eval (State (Sub (Prompt p) y x) d es q) = State (Prompt p) d es q
eval (State (Sub NewPrompt y x) d es q) = State NewPrompt d es q
eval (State (Sub (PushPrompt e1 e2) y x) d es q) = State (PushPrompt (Sub e1 y x) (Sub e2 y x)) d es q
eval (State (Sub (WithSubCont e1 e2) y x) d es q) = State (WithSubCont (Sub e1 y x) (Sub e2 y x)) d es q
eval (State (Sub (PushSubCont e1 e2) y x) d es q) = State (PushSubCont (Sub e1 y x) (Sub e2 y x)) d es q

eval (State NewPrompt d es (Prompt p)) = State (Prompt p) d es (Prompt $ p+1)

-- explicit returning
eval (State v d es q) = case d of
  Hole -> case es of
    (e:es') -> case e of
      Prompt p -> State v Hole es' q
      otherwise -> State v e es' q
    otherwise -> State v d es q
  otherwise -> State (Return d v) Hole es q
  
eval (State (Return d' v) d es q) = State filled d es q
  where filled = case d of
          Hole -> v
          App Hole e -> App v e
          App e Hole -> App e v
          PushPrompt Hole e -> PushPrompt v e
          WithSubCont Hole e -> WithSubCont v e
          WithSubCont e Hole -> WithSubCont e v
          PushSubCont Hole e -> PushSubCont v e
   
promptMatch :: Int -> Expr -> Bool
promptMatch i p = case p of
  Prompt p' -> i == p'
  otherwise -> False
  
splitBefore p es = takeWhile (not . promptMatch p) es
splitAfter  p es = case length es of
  0 -> []
  otherwise -> tail list
  where list = dropWhile (not . promptMatch p) es
 
evalFull s = do
  putStrLn $ (prettifyState s) ++ "\t" ++ (show s)
  let s' = eval s in
    if s == s' then 
      putStrLn "terminated"
    else 
      evalFull s'
      
vx = State (Var 'x') Hole [] (Prompt 0)
np = State NewPrompt Hole [] (Prompt 0)
ap = State (Var 'y') (App (Abs 'x' (Var 'x')) Hole) [] (Prompt 0)
