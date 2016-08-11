--{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}
--{-# LANGUAGE StandaloneDeriving #-}

module DCC where 

import Data.List

data Value = Var Char
  | Abs Char Expr
  | Prompt Int
  deriving (Show, Eq)
  
data Expr = Val Value 
  | App Expr Expr
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

prettify (Val v) = case v of
  Var c -> [c]
  Abs h m -> mconcat [ "(\\", [h], ".", prettify m, ")" ]
  Prompt i -> show i

prettify (App m n) = mconcat ["(", prettify m, prettify n, ")" ]
prettify NewPrompt = " np"
prettify (PushPrompt e1 e2) = mconcat ["(pp ", prettify e1, " ", prettify e2, ")"]
prettify (WithSubCont e1 e2) = mconcat ["(wsc ", prettify e1, " ", prettify e2, ")"]
prettify (PushSubCont e1 e2) = mconcat ["(psc ", prettify e1, " ", prettify e2, ")"]
prettify Hole = "_"
prettify (Seq es) = foldr (++) "" $ intersperse ":" $ map prettify es

prettify (Sub e1 e2 c) = mconcat [ prettify e1, "[", prettify e2, "/", [c], "]" ]
prettify (Return d v) = prettify $ ret d v

prettifyState :: State -> String
prettifyState (State e d es q) = mconcat ["(", prettify e, ", ", prettify d, if (length es) == 0 then ", [], " else ", E, ", prettify (Val q), ")" ]

data State = State Expr Expr [Expr] Value
  deriving (Show, Eq)

shiftContext :: State -> Expr -> State
shiftContext (State e d es q) d' = case d of
  Hole -> (State e d' es q)
  otherwise -> (State e (Return d d') es q)
  
contextToAbs :: Expr -> Expr 
contextToAbs e = (Val (Abs fresh body))
  where fresh = 'x'  -- TODO: generate truly fresh var
        body = ret e (Val (Var fresh))

ret :: Expr -> Expr -> Expr
ret d e = case d of
  Hole -> e
  App m n -> App (ret m e) (ret n e)
  Val (Abs x m) -> Val $ Abs x (ret m e)
  PushPrompt m n -> PushPrompt (ret m e) (ret n e)
  WithSubCont m n -> WithSubCont (ret m e) (ret n e)
  PushSubCont m n -> PushSubCont (ret m e) (ret n e)
  otherwise -> d

seqToAbs :: [Expr] -> Expr
seqToAbs es = contextToAbs $ foldr ret Hole $ reverse es
  
exprs = [(App Hole (Val (Var 's'))), (App (Val (Var 't')) Hole), App (Val (Var 'u')) Hole]
app = seqToAbs exprs

-- TODO: resolve overlapping cases
eval :: State -> State
eval (State (App e e') d es q) = case e of
  Val v -> case e' of 
    Val _ -> case v of (Abs x e) -> State (Sub e e' x) d es q
    otherwise -> shiftContext (State e' d es q) (App e Hole)
  otherwise -> State e (Return d (App Hole e')) es q


eval (State (PushPrompt e e') d es q) = case e of
  Val _ -> State e' Hole (e:d:es) q
  otherwise -> case d of
    Hole -> State e (PushPrompt Hole e') es q
    otherwise -> State e (Return d (PushPrompt Hole e')) es q

--eval (State (WithSubCont e e') d es q) = case e of
--  Val v ->
--  otherwise -> State e

eval (State (WithSubCont e e') d es q) = case e of
  Val v -> case e' of
    Val _ -> case v of (Prompt p) -> State (App e' (Seq (d:(splitBefore p es)))) Hole (splitAfter p es) q
    otherwise -> shiftContext (State e' d es q) (WithSubCont e Hole)
  otherwise -> shiftContext (State e d es q) (WithSubCont Hole e')
    
eval (State (PushSubCont e e') d es q) = case e of
  Val _ -> case e of (Seq s) -> State e Hole (s++(d:es)) q
  otherwise -> State e (Return d (PushSubCont Hole e')) es q


eval (State (Sub (Val (Var m)) v x) d es q) = State (if m == x then v else (Val (Var m))) d es q
eval (State (Sub (Val (Abs h m)) y x) d es q) = State (Val (Abs h (sub m y x))) d es q
eval (State (Sub (App m n) y x) d es q) = State (App (sub m y x) (sub n y x)) d es q
eval (State (Sub (Val (Prompt p)) y x) d es q) = State (Val (Prompt p)) d es q
eval (State (Sub NewPrompt y x) d es q) = State NewPrompt d es q
eval (State (Sub (PushPrompt e1 e2) y x) d es q) = State (PushPrompt (sub e1 y x) (sub e2 y x)) d es q
eval (State (Sub (WithSubCont e1 e2) y x) d es q) = State (WithSubCont (sub e1 y x) (sub e2 y x)) d es q
eval (State (Sub (PushSubCont e1 e2) y x) d es q) = State (PushSubCont (sub e1 y x) (sub e2 y x)) d es q

eval (State NewPrompt d es (Prompt p)) = State (Val (Prompt p)) d es (Prompt $ p+1)

-- explicit returning
eval (State (Val v) d es q) = case d of
  Hole -> case es of
    (e:es') -> case e of
      (Val (Prompt p)) -> State (Val v) Hole es' q
      otherwise -> State (Val v) e es' q
    otherwise -> State (Val v) d es q
  otherwise -> State (Return d (Val v)) Hole es q

eval (State (Return d' v) d es q) = State (ret d' v) d es q
          
eval (State (Seq s) d es q) = State (seqToAbs s) d es q
     
sub :: Expr -> Expr -> Char -> Expr
sub m v x = case m of
  Val (Var n) -> if n == x then v else m
  Val (Abs y e) -> Val (Abs y $ sub e v x)
  Val (Prompt p) -> Val (Prompt p)
  App e e' -> App (sub e v x) (sub e' v x)
  NewPrompt -> NewPrompt
  PushPrompt e e' -> PushPrompt (sub e v x) (sub e' v x)
  WithSubCont e e' -> WithSubCont (sub e v x) (sub e' v x)
  PushSubCont e e' -> PushSubCont (sub e v x) (sub e' v x)
   
promptMatch :: Int -> Expr -> Bool
promptMatch i p = case p of
  (Val (Prompt p')) -> i == p'
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
      
vx = State (Val (Var 'x')) Hole [] (Prompt 0)
np = State NewPrompt Hole [] (Prompt 0)
ap = State (Val (Var 'y')) (App (Val (Abs 'x' (Val (Var 'x')))) Hole) [] (Prompt 0)
es = State (Val (Var 'y')) Hole [(App (Val (Abs 'x' (Val (Var 'x')))) Hole)] (Prompt 0)
es' = State (Val (Abs 'y' (Val (Var 'y')))) Hole [(App Hole (Val (Var 'x')))] (Prompt 0)
es'' = State (Val (Abs 'y' (Val (Var 'y')))) Hole [(App Hole (Val (Abs 'x' (Val (Var 'x'))))),(App Hole (Val (Var 'z')))] (Prompt 0)

wsc = State (App (Val (Abs 'a' (PushPrompt (Val (Var 'a')) (WithSubCont (Val (Var 'a')) (Val (Abs 'k' (Val (Var 'x'))))) )))
            NewPrompt) Hole [] (Prompt 0)

wsc' = State (App (Val (Abs 'a' (PushPrompt (Val (Var 'a')) (App (WithSubCont (Val (Var 'a')) (Val (Abs 'k' (Val (Var 'x'))))) (Val (Var 'z'))))))
            NewPrompt) Hole [] (Prompt 0)
