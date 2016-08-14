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
  
  | Sub Expr Expr Char
  deriving (Show, Eq)

data State = State Expr Expr [Expr] Value
  deriving (Show, Eq)

prettify :: Expr -> String
prettify (Val (Var c)) = [c]
prettify (Val (Abs h m)) = mconcat [ "(\\", [h], ".", prettify m, ")" ]
prettify (Val (Prompt i)) = show i
prettify (App m n) = mconcat ["(", prettify m, prettify n, ")" ]
prettify NewPrompt = " np"
prettify (PushPrompt e1 e2) = mconcat ["(pp ", prettify e1, " ", prettify e2, ")"]
prettify (WithSubCont e1 e2) = mconcat ["(wsc ", prettify e1, " ", prettify e2, ")"]
prettify (PushSubCont e1 e2) = mconcat ["(psc ", prettify e1, " ", prettify e2, ")"]
prettify Hole = "_"
prettify (Seq es) = foldr (++) "" $ intersperse ":" $ map prettify es
prettify (Sub e1 e2 c) = mconcat [ prettify e1, "[", prettify e2, "/", [c], "]" ]

prettifyState :: State -> String
prettifyState (State e d es q) = mconcat ["(", prettify e, ", ", prettify d, if (length es) == 0 then ", [], " else ", E, ", prettify (Val q), ")" ]

-- create abstractions from context e.g
-- D[] -> (\x.D[x])
contextToAbs :: Expr -> Expr 
contextToAbs e = (Val (Abs fresh body))
  where fresh = 'x'  -- TODO: generate truly fresh var
        body = ret e (Val (Var fresh))

-- replace hole of first expr with second expr e.g
-- D [] -> [] C -> D ([] C)
-- final expr should one hole (on condition that first
-- and second have one hole each). if first expr has
-- no hole, first expr is returned
ret :: Expr -> Expr -> Expr
ret d e = case d of
  Hole -> e
  App m n -> App (ret m e) (ret n e)
  Val (Abs x m) -> Val $ Abs x (ret m e)
  PushPrompt m n -> PushPrompt (ret m e) (ret n e)
  WithSubCont m n -> WithSubCont (ret m e) (ret n e)
  PushSubCont m n -> PushSubCont (ret m e) (ret n e)
  otherwise -> d

-- fold sequence of terms with holes into abs with one argument e.g
-- [] M : N [] : O [] -> \x. O (N (x M)
-- in effect, this produces an abstraction that when applied to a value
-- v has the effect of returning v to the continuation represented
-- by the sequence
seqToAbs :: [Expr] -> Expr
seqToAbs es = contextToAbs $ foldr ret Hole $ reverse es

-- reduction rules
eval :: State -> State
eval (State (App e e') d es q) = case e of
  Val v -> case e' of 
    Val _ -> case v of (Abs x m) -> State (Sub m e' x) d es q
    otherwise -> State e' (ret d (App e Hole)) es q
  otherwise -> State e (ret d (App Hole e')) es q

eval (State (PushPrompt e e') d es q) = case e of
  Val _ -> State e' Hole (e:d:es) q
  otherwise -> case d of
    Hole -> State e (PushPrompt Hole e') es q
    otherwise -> State e (ret d (PushPrompt Hole e')) es q

eval (State (WithSubCont e e') d es q) = case e of
  Val v -> case e' of
    Val _ -> case v of (Prompt p) -> State (App e' (Seq (d:beforeP))) 
                                            Hole afterP q
                                     where beforeP = splitBefore p es
                                           afterP = splitAfter p es
    otherwise -> State e' (ret d (WithSubCont e Hole)) es q 
  otherwise -> State e (ret d (WithSubCont Hole e')) es q 
  
-- TODO: this might break if e contains a prompt that
-- a future operation (withsubcont?) needs access to.
-- could break some edge cases.
eval (State (PushSubCont e e') d es q) = case e of
  -- HACK: When pushing e onto stack, apply to hole to
  --       counteract premature conversion of context
  --       into abstraction
  Val v -> State e' Hole ([App (Val v) Hole]++(d:es)) q
  otherwise -> State e (ret d (PushSubCont Hole e')) es q

eval (State (Sub e y x) d es q) = State e' d es q
  where e' = case e of
          Val (Var m) -> if m == x then y else (Val (Var m))
          Val (Abs h m) -> Val (Abs h (sub m y x))
          App m n -> App (sub m y x) (sub n y x)
          Val (Prompt p) -> Val (Prompt p)
          NewPrompt -> NewPrompt
          PushPrompt e1 e2 -> PushPrompt (sub e1 y x) (sub e2 y x)
          WithSubCont e1 e2 -> WithSubCont (sub e1 y x) (sub e2 y x)
          PushSubCont e1 e2 -> PushSubCont (sub e1 y x) (sub e2 y x)

eval (State NewPrompt d es (Prompt p)) = State (Val (Prompt p)) 
                                               d es (Prompt $ p+1)

-- returning values to contexts
eval (State (Val v) d es q) = case d of
  Hole -> case es of
    (e:es') -> case e of
      (Val (Prompt p)) -> State (Val v) Hole es' q
      otherwise -> State (Val v) e es' q
    otherwise -> State (Val v) d es q
  otherwise -> State (ret d (Val v)) Hole es q

eval (State (Seq s) d es q) = State (seqToAbs s) d es q

-- replace all occurences in m of x with v
-- m[v/x] e.g
-- M x -> y -> x -> M y
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

-- utility function for matching prompts
promptMatch :: Int -> Expr -> Bool
promptMatch i p = case p of
  (Val (Prompt p')) -> i == p'
  otherwise -> False
  
-- returns sequence of expressions UP UNTIL prompt p (not incl)
splitBefore p es = takeWhile (not . promptMatch p) es
-- returns sequence of expressions FROM prompt p (not incl)
splitAfter  p es = case length es of
  0 -> []
  otherwise -> tail list
  where list = dropWhile (not . promptMatch p) es

-- evaluates expression to termination (runs interpreter)
evalFull s = do
  putStrLn $ (prettifyState s) ++ "\t" ++ (show s)
  let s' = eval s in
    if s == s' then 
      putStrLn "terminated"
    else 
      evalFull s'
      
run s = 
  let s' = eval s in
    if s == s' then s else run s'

-- sample data
vx = State (Val (Var 'x')) Hole [] (Prompt 0)
ap = State (Val (Var 'y')) (App (Val (Abs 'x' (Val (Var 'x')))) Hole) [] (Prompt 0)
es = State (Val (Var 'y')) Hole [(App (Val (Abs 'x' (Val (Var 'x')))) Hole)] (Prompt 0)
es' = State (Val (Abs 'y' (Val (Var 'y')))) Hole [(App Hole (Val (Var 'x')))] (Prompt 0)
es'' = State (Val (Abs 'y' (Val (Var 'y')))) Hole [(App Hole (Val (Abs 'x' (Val (Var 'x'))))),(App Hole (Val (Var 'z')))] (Prompt 0)

exprs = [(App Hole (Val (Var 's'))), (App (Val (Var 't')) Hole), App (Val (Var 'u')) Hole]
app = seqToAbs exprs

-- combinators
i = (Val (Abs 'x' (Val (Var 'x'))))
k = (Val (Abs 'x' (Val (Abs 'y' (Val (Var 'x'))))))
s = (Val (Abs 'x' (Val (Abs 'y' (Val (Abs 'z' (App (App (var 'x') (var 'z')) (App (var 'y') (var 'z')))))))))

f = abst 'x' (var 'f')

var :: Char -> Expr
var = Val . Var 
abst :: Char -> Expr -> Expr
abst c = Val . Abs c

wsc :: Expr -> Expr -> Expr
wsc e e' = WithSubCont e e'

psc :: Expr -> Expr -> Expr
psc e e' = PushSubCont e e'

np :: Expr
np = NewPrompt

pp :: Expr -> Expr -> Expr
pp e e' = PushPrompt e e'

state :: Expr -> State
state e = State e Hole [] (Prompt 0)

app3 x y z = App (App x y) z
skk = app3 s k k
sks = app3 s k s

test0 = evalFull . state $ App (App k (var 'u')) (var 't')
test1 = evalFull . state $ App skk (var 'u')
test2 = evalFull . state $ App sks (var 'u')

test3 = evalFull . state $ App (abst 'p' (pp (var 'p') (App (wsc (var 'p') (abst 'a' (App (var 'a') (var 's')))) (var 't')))) np
test4 = evalFull . state $ App (abst 'p' (pp (var 'p') (App (wsc (var 'p') (abst 'a' (psc (var 'a') (var 's')))) (var 't')))) np
test5 = evalFull . state $ App (abst 'p' (pp (var 'p') (App (wsc (var 'p') (abst 'a' (App (psc (var 'a') k) (psc (var 'a') f)))) (var 't')))) np

--evalExpr = evalFull . state
--equality1 e = evalFull i e == evalFull skk e
