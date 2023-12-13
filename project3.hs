--Project 

import System.IO
import Data.Char
import Data.List
import Data.Maybe

--Types, Terms, Tokens

type Vars = String
type TVars = String
type FName = String

data Types = Natural | TVar TVars | Fun Types Types | Prod Types Types
  deriving (Show,Eq)

data Terms = Var Vars | App Terms Terms | Abs Vars Terms 
    | Zero | Succ Terms | Rec Terms Terms Terms | Pair Terms Terms 
    | Fst Terms | Snd Terms | Def FName Terms
    deriving (Show,Eq)

data Token = VSym Vars | LPar | RPar | Dot | Backslash |
        Err String | ZeroT | SuccT | RecT | CommaT | FstT | SndT | PT Terms 
    deriving (Show)

--Lexer

lexer :: String -> [Token]
lexer "" = []
lexer ('.':s) = (Dot : lexer s)
lexer ('\\':s) = (Backslash : lexer s)
lexer (',':s) = (CommaT : lexer s)
lexer ('(':s) = (LPar : lexer s)
lexer (')':s) = (RPar : lexer s)
lexer ('S':s) = (SuccT : lexer s)
lexer ('0':s) = (ZeroT : lexer s)
lexer s | isPrefixOf "fst" s  = FstT : lexer (drop 3 s)
lexer s | isPrefixOf "snd" s  = SndT : lexer (drop 3 s)
lexer s | isPrefixOf "recursion" s  = RecT : lexer (drop 9 s)                 
lexer (c:s) | isLower c = let (var,rst) = span isAlphaNum s
                            in (VSym (c:var) : lexer rst)
lexer (c:s) | isSpace c = lexer s
lexer (c:s) = (Err ("Invalid character " ++ [c]) : lexer s)                

--Parser

parser :: [Token] -> Either Terms String
parser ts = case sr [] ts of
  [PT t]  -> Left t
  []      -> Right ""
  [Err e] -> Right e
  st      -> Right $ "Parse error: " ++ show st

--Shift Reduce

sr :: [Token] -> [Token] -> [Token]
sr (VSym x : s)                              q = sr (PT (Var x)     : s) q
sr (ZeroT : s)                              q = sr (PT (Zero)     : s) q
sr (RPar : PT e3 :CommaT: PT e2 :CommaT : PT e1 : LPar : RecT : s) q = sr (PT (Rec e1 e2 e3) : s) q
sr (PT e2 : PT e1 : s)                       q = sr (PT (App e1 e2) : s) q               
sr (RPar :PT e2 : CommaT : PT e1 : LPar : s)                       q = sr (PT (Pair e1 e2) : s) q
sr (PT e1 : FstT : s)                       q = sr (PT (Fst e1) : s) q
sr (PT e1 : SndT : s)                       q = sr (PT (Snd e1) : s) q
sr (PT e1 : Dot : PT (Var x) : Backslash : s)  q = sr (PT (Abs x e1)  : s) q
sr (PT e1 : SuccT : s)               q = sr (PT (Succ e1) : s) q
sr (RPar : PT e1 : LPar : s)                     q = sr (PT e1 : s) q
sr (Err e : ts) i = [Err e]
sr st      (i:is) = sr (i:st) is
sr st          [] = st

--Substitute

subst :: (Vars,Terms) -> Terms -> Terms
subst (v,t) (Zero) = Zero
subst (v,t) (Var x) = if x == v then t else (Var x)
subst (v,t) (App e1 e2) = App (subst (v,t) e1) (subst (v,t) e2)
subst (v,t) (Succ e1) = Succ (subst (v,t) e1)
subst (v,t) (Pair e1 e2) = Pair (subst (v,t) e1) (subst (v,t) e2)
subst (v,t) (Fst e1) = Fst (subst (v,t) e1)
subst (v,t) (Snd e1) = Snd (subst (v,t) e1)
subst (v,t) (Rec e1 e2 e3) = Rec (subst (v,t) e1) (subst (v,t) e2) (subst (v,t) e3)
subst (x,s) t@(Abs y r)                                                                     -- from lecture 11.17
  | x == y              = t
  | not (elem y (fv t)) = Abs y (subst (x,s) r)
  | otherwise           =
      let y' = freshVar (x : y : fv s ++ fv t)
          r' = subst (y,Var y') r
       in Abs y' (subst (x,s) r')

fv :: Terms -> [Vars]
fv (Zero) = []
fv (Var x) = [x]
fv (App s t) = nub $ fv s ++ fv t
fv (Abs x t) = filter (/= x) (fv t)
fv (Pair s t) = nub $ fv s ++ fv t
fv (Rec t1 t2 t3) = nub $ fv t1 ++ fv t2 ++ fv t3
fv (Succ t) = fv t
fv (Fst t) = fv t
fv (Snd t) = fv t

--predStep

predStep :: Terms -> Terms
--root reduction steps
predStep (App (Abs x s) t) = subst (x,t) s
predStep (Rec z f Zero) = z
predStep (Rec z f (Succ n)) = App (App f n) (Rec z f n)
predStep (Fst (Pair x y)) = x
predStep (Snd (Pair x y)) = y
--congruence rules
predStep (Var x) = Var x
predStep (Abs x m) = Abs x (predStep m) 
predStep (App x m) = App (predStep x) (predStep m)
predStep (Zero) = Zero
predStep (Succ x) = Succ (predStep x)
predStep (Rec x m y) = Rec (predStep x) (predStep m) (predStep y)
predStep (Pair x m) = Pair (predStep x) (predStep m)
predStep (Fst x) = Fst (predStep x)
predStep (Snd x) = Snd (predStep x)

preds :: Terms -> Terms
preds t = let t' = predStep t
           in if t == t' then t else preds t'
           
--Typing

allVars :: [String]
allVars = "" : newVars
  where newVars = allVars >>= (\var -> [ var ++ [l] | l <- ['a'..'z']])

freshVar :: [String] -> String
freshVar vs =
  let inds = catMaybes (map (\x -> elemIndex x allVars) ("":vs))
   in allVars !! (maximum inds + 1)

type Constr = (Types,Types)
type Context = [(Vars,Types)]
type TSub = [(TVars,Types)]


tsubst :: (TVars,Types) -> Types -> Types                                   
tsubst (a,t) (Natural) = Natural                                         
tsubst (a,t) (TVar b) | a == b = t
                    | otherwise = TVar b
tsubst (a,t) (Fun t1 t2)  = Fun (tsubst (a,t) t1) (tsubst (a,t) t2 )
tsubst (a,t) (Prod t1 t2)  = Prod (tsubst (a,t) t1) (tsubst (a,t) t2 )


tsubC :: (TVars,Types) -> [Constr] -> [Constr]
tsubC at [] = []
tsubC at ((l,r) : cs) = (tsubst at l , tsubst at r) : tsubC at cs

substAll :: TSub -> Types -> Types
substAll [] t = t
substAll (at:ts) t = substAll ts (tsubst at t)


ftv :: Types -> [TVars]                          
ftv (Natural) = []
ftv (TVar a) = [a]
ftv (Fun t1 t2) = ftv t1 ++ ftv t2
ftv (Prod t1 t2) = ftv t1 ++ ftv t2


ftvC :: Context -> [TVars]
ftvC [] = []
ftvC ((x,a) : g) = ftv a ++ ftvC g


genConstr :: Context -> Terms -> Types -> [Constr]                
genConstr g (Zero) a = [] 
genConstr g (Var x) a = case lookup x g of
                          Just b  -> [(a,b)]
                          Nothing -> error ("Variable not found in context: " ++ x)
genConstr g (App s t) b =
  let a = freshVar (ftv b ++ ftvC g)
      c1 = genConstr g s (Fun (TVar a) b)
      c2 = genConstr g t (TVar a)
   in c1 ++ c2
genConstr g (Abs x r) b =
  let a1 = freshVar (ftv b ++ ftvC g)
      a2 = freshVar (a1 : (ftv b ++ ftvC g))
   in (b , Fun (TVar a1) (TVar a2)) : genConstr ((x,TVar a1):g) (r) (TVar a2)
genConstr g (Succ t) b = genConstr g t (Natural)
genConstr g (Rec t1 t2 t3) b = 
  let c1 = genConstr g t1 (b)
      c2 = genConstr g t2 (Fun Natural (Fun (b) (b)))           -- correct order?
      c3 = genConstr g t3 (Natural)
  in c1 ++ c2 ++ c3
genConstr g (Fst s) a = 
  let b = freshVar (ftv a ++ ftvC g)
      in genConstr g s (Prod (TVar b) (a))
genConstr g (Snd s) b = 
  let a = freshVar (ftv b ++ ftvC g)
      in genConstr g s (Prod (TVar a) (b))
genConstr g (Pair s t) b =
  let a1 = freshVar (ftv b ++ ftvC g)
      a2 = freshVar (a1 : (ftv b ++ ftvC g))
      c1 = genConstr g s (TVar a1)
      c2 = genConstr g t (TVar a2)
   in (b , Prod (TVar a1) (TVar a2)) : (c1 ++ c2)

solve :: [Constr] -> TSub
solve [] = []
solve ((TVar a, TVar b) : cs) | a == b = solve cs
solve ((TVar a, t) : cs) | a `elem` ftv t = error "Circular type!"
                         | otherwise = (a,t) : solve (tsubC (a,t) cs)
solve ((t,TVar a) : cs) = solve ((TVar a , t) : cs)
solve ((Fun s1 s2 , Fun t1 t2) : cs) = solve ((s1,t1) : (s2,t2) : cs)
solve ((Prod s1 s2 , Prod t1 t2) : cs) = solve ((s1,t1) : (s2,t2) : cs)
solve ((Natural, Natural) : cs) = solve cs                                     
solve _ = error "Type error!"



infer :: Terms -> Types
infer t =
  let cs = genConstr [] t (TVar "a")
      ts = solve cs
   in substAll ts (TVar "a")


main :: IO ()
main = do
  putStrLn "Enter the name of the input file:"
  fileName <- getLine
  contents <- readFile fileName
  let functionList = parseFileContents contents
  putStrLn "Functions loaded successfully!"
  putStrLn "Parsed functions:"
  print functionList
  loop functionList

loop :: [(FName, Terms)] -> IO ()
loop functionList = do

  putStrLn "Enter an expression to evaluate (or type 'exit' to quit):"
  expression <- getLine
  if expression == "exit"
    then putStrLn "Exiting program."
    else do
      let parsedExpression = parseExpression expression
          substitutedExpression = substituteFunctions functionList parsedExpression
          inferredType = infer substitutedExpression
          result = preds substitutedExpression
      putStrLn $ "Inferred type: " ++ show inferredType
      putStrLn $ "Result: " ++ show result
      loop functionList


parseFileContents :: String -> [(FName, Terms)]
parseFileContents = map parseLine . lines
  where
    parseLine :: String -> (FName, Terms)
    parseLine line =
      case words line of
        (name: "=" : rest) ->
          let tokens = lexer $ unwords rest
          in case parser tokens of
               Left expr -> (trim name, expr)
               Right err -> error $ "Expression parsing error: " ++ err ++ "\nLexer output: " ++ show tokens
        _ -> ([],Zero)




trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse


substituteFunctions :: [(FName, Terms)] -> Terms -> Terms
substituteFunctions [] expr = expr
substituteFunctions ((name, body):fs) expr =
  substituteFunctions fs $ subst (name, body) expr


parseExpression :: String -> Terms
parseExpression input = case parser $ lexer input of
  Left expr -> expr
  Right err -> error $ "Expression parsing error: " ++ err
