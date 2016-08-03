--{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
--{-# LANGUAGE StandaloneDeriving #-}

{-
    Implementation of abstract machine semantics for Simon 
    Peyton-Jones's Delimited-Continuation Calculus (DCC). 
    All steps should be explicit to observe evolution of
    state through evaluation process.
-}

-- DataKinds allows us to restrict over kind arguments

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
--
--data Expr (n :: ExprType) where
--  Var :: Char -> Expr Value
--  Abs :: Expr Value -> Expr n -> Expr Value
--  App :: Expr Value -> Expr n -> Expr Redex
--   
--  Sub :: Expr n -> Expr n -> Char -> Expr Redex
--
--  NewPrompt :: Expr Redex
--  PushPrompt :: Expr Prompt -> Expr n -> Expr Redex
--  WithSubCont :: Expr n -> Expr n -> Expr Redex
--  PushSubCont :: Expr n -> Expr n -> Expr Redex
--  
  
  --NewPrompt
  --PushPrompt Expr Expr
  --WithSubCont Expr Expr
  --PushSubCont Expr Expr
  --Hole
  --Prompt Int
  --Compose [Expr] [Expr]  -- for composing frames

--cool = [] :: List (Expr ExprType)
--deriving instance Eq (Expr n)

data State = State Expr Expr [Frame] Expr
  deriving (Show, Eq)
  
--splitBefore :: [Expr] -> Expr -> [Expr]
--splitBefore (e:es) p
--  | p /= e    = e:(splitBefore es p)
--  | otherwise = [e]
--splitBefore [] p = []
--
--splitAfter :: [Expr] -> Expr -> [Expr]
--splitAfter (e:es) p
--  | p /= e = splitAfter es p
--  | otherwise = es
--splitAfter [] p = []

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

--eval (State (Val v) d es q) = State (App (Val v) d) Hole es q
--eval (State (Val v) Hole es q) = case length es of
--  0 -> State (Val v) Hole es q
--  otherwise -> State (Val v) (extractFrame $ head es) q

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
--eval (State (Var x) d es q) = State (App (Var x) d) Hole es q
--eval (State (Abs x m) d es q) = State (App (Abs x m) d) Hole es q
--eval (State v d (e:es) q) = case d of
--  Hole -> (State (App v d) Hole es q)
--  otherwise -> case e of
--    Prompt _  -> (State v Hole es q) 
--    otherwise -> (State v e es q) 
   


--data Expr :: * -> * where
--  Var :: Char -> Expr Char
--  Abs :: Char -> Expr a -> Expr a
--  App :: Expr Char -> Expr a -> Expr a
--  Sub :: Expr a -> Expr a -> Char -> Expr a
--  
--  P :: Int -> Expr Int
--  NewPrompt :: Expr Int
--  PushPrompt :: Expr Int -> Expr a -> Expr a
--  WithSubCont :: Expr a -> Expr a -> Expr a
--  PushSubCont :: Expr a -> Expr a -> Expr a
--  Hole :: Expr Empty
--
--deriving instance Show (Expr a)
--deriving instance Eq (Expr a)
--
--data State a  = State (Expr a) (Expr a) [(Expr a)] (Expr Int)
--  deriving (Show, Eq)
--
--eval :: State a -> State a
--eval x = x

-- returning a value
--eval (State v d (e:es) q) = (State (App v d) e es q)

--data State = State (Expr a) Int [(Int, (Expr a))]
--  deriving (Show, Eq)

--data State a = State (Expr a) (Expr Int) [Expr a] (Expr Int)
--  deriving (Show, Eq)

--show(Expr a) :: (Expr a) -> String
--show(Expr a) (Var x) = [x]
--show(Expr a) (Abs h b) = "(\\" ++ [h] ++ "." ++ (show(Expr a) b) ++ ")"
--show(Expr a) (App m n) = show(Expr a) m ++ (show(Expr a) n)
--show(Expr a) (Sub e1 e2 c) = show(Expr a) e1 ++ "[" ++ (show(Expr a) e2) ++ "/" ++ [c] ++ "]"
--
--show(Expr a) (NewPrompt) = "newPrompt"
--show(Expr a) (PushPrompt p exp) = "pushPrompt " ++ (show p) ++ (show exp)
--show(Expr a)  (P i) = "p(" ++ (show i) ++ ")"
--
--showState :: State -> String
--showState (State expr q e) = "(" ++ (show(Expr a) expr) ++ ", " ++ (show q) ++ ", " ++ (show e) ++ ")"
--
--eval :: State -> State
--eval (State (Var a) q e)            = (State (Var a) q e)
--eval (State NewPrompt q e)          = (State (P q) (q+1) e)
--eval (State (PushPrompt p ex) q  e) = (State ex q ((p, ex):e))
--
--test(Expr a) expr = showState $ eval (State expr 0 [])
--test expr = showState $ eval expr
