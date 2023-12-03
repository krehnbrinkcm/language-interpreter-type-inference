import Data.Char (isAlphaNum,isSpace,isDigit,isLower)
import Data.List (isPrefixOf,elemIndex,nub)
import Data.Maybe (catMaybes)

-- Haskell Representation of PCF Syntax

type Vars = String
type TVars = String

data Types = Int | Bool | Unit | Fun Types Types | Prod Types Types | TVar TVars deriving Show

data Terms = Var String | Var Vars| App Terms Terms | Abs Vars Terms
           | Const Integer | Add Terms Terms | Leq Terms Terms 
           | Tru | Fls | IfThenElse | Pair Terms Terms 
           | Fst Terms | Snd Terms | Y
           deriving (Show,Eq)

data Token = VSym String | CSym Integer 
           | AddOp | LeqOp | TrueK | FalseK | IfPositiveK | ThenK | ElseK
           | PairK | FstK | SndK | Ycomb
           | LPar | RPar | Comma | Dot | Backslash | UnitK
           | Err String | PT Terms
           deriving (Eq,Show)

-- Part 1. Parsing and Lexical Analysis
 
 --may need to remove some of these
lexer :: String -> [Token]
lexer ('+':s) = AddOp : lexer s 
lexer ('Y':s) = YComb : lexer s
-- LeqOp
-- pair
-- fst
-- snd
lexer s | isPrefixOf "ifPositive" s = IfPositiveK : lexer (drop 10 s)
lexer s | isPrefixOf "then" s = ThenK : lexer (drop 4 s)
lexer s | isPrefixOf "else" s = ElseK : lexer (drop 4 s)
lexer ('(':s) = LPar : lexer s
lexer (')':s) = RPar : lexer s
lexer ('.':s) = Dot : lexer s
lexer (',':s) = Comma : lexer s
-- unit
lexer ('\\':s) = Backslash : lexer s 
lexer s@(c:_) | isDigit c = CSym (read n) : lexer t where (n,t) = span isDigit s
lexer s@(v:_) | isLower v = VSym n : lexer t where (n,t) = span isAlphaNum s
lexer (w:s) | isSpace w = lexer s
lexer "" = []
lexer s = [Err s]

parser :: [Token] -> Either Terms String
parser ts = case sr [] ts of
    [PT t] -> Left t
    [Err s] -> Right ("Lexical error: " ++ s)
    s -> Right ("Parse error: " ++ show s)

sr :: [Token] -> [Token] -> [Token]
sr (CSym n : ts) i = sr (PT (Const n) : ts) i
sr (VSym n : ts) i = sr (PT (Var n) : ts) i
sr (YComb : ts) i = sr (PT Y : ts) i
-- subop line
-- ifpos line
sr (RPar : PT t : LPar : ts) i = sr (PT t : ts) i
-- abs line
-- app line
sr m (i0:i) = sr (i0:m) i
sr st [] = st

--ALL ELSE HAS NOT BEEN CHECKED
-- Part 2. Reduction

allVars :: [Vars]
allVars = ("" : allVars) >>= (\s -> (map (\x -> s ++ [x]) ['a'..'z']))

freshVar :: [Vars] -> Vars
freshVar vs = allVars !! (maximum (catMaybes (elemIndex x allVars | x <- xs)) + 1)
    where xs = nub vs

fv :: Terms -> [Vars]
fv (Var x) = [x]
fv (Abs x r) = filter (/= x) (fv r)
fv (App r s) = nub $ fv s ++ fv r
fv (Sub s t) = nub $ fv s ++ fv t
fv (IfPos r s t) = nub $ fv r ++ fv s ++ fv t
fv _ = []

-- Question 2.1
subst :: (Vars,Terms) -> Terms -> Terms
subst (x,t) (Var y) | x==y = t
                    | otherwise = (Var y)
subst (x,t) (Abs y r) | x == y = Abs y r
                      | not (elem y (fv t)) = Abs y (subst (x,t) r)
subst (x,t) (Abs y r)
    let z = freshVar (x : y : fv t ++ fv r)
        r' = subst (y,Var z) r
    in Abs z (subst (x,t) r')

-- constant case when c is Const n or Y
-- ...
-- Question 2.2
predstep :: Terms -> Terms
predstep (App (Abs x t) s) = subst (x,s) t
predstep (App (Const n) _) = Const n -- constant case
predstep (App (IfPos (Const n) t1 t2) t) = if n > 0 then t1 else t2
predstep (Sub (Const m) (Const n)) = Const (m - n)
predstep (App Y t) = App t (App Y t)
predstep (IfPos r s t) = IfPos (predstep r) (predstep s) (predstep t)
-- Congruence rules
predstep (Abs x r) = Abs x (predstep r)
predstep (App s t) = App (predstep s) (predstep t)
predstep (Sub s t) = Sub (predstep s) (predstep t)
predstep (IfPos r s t) = IfPos (predstep r) (predstep s) (predstep t)
-- Reflexivity for variables, constants, and Y (the leaves of syntax tree)
predstep x = x

-- Question 2.3
preds :: Terms -> Terms
preds t = if t == t' then t else preds t' where t' = predstep t

-- Part 3. Typing

type Constr = (Types,Types)
type Context = [(Vars,Types)]

ftv :: Types -> [TVars]
ftv (TVar a) = [a]
ftv (Fun t1 t2) = ftv t1 ++ ftv t2

ftvc :: Context -> [TVars]
ftvc gamma = map snd gamma >>= ftv

-- Question 3.1
tsubst :: (TVars,Types) -> Types -> Types
tsubst (a,t) (TVar b) | a == b = t
                      | otherwise = TVar b
tsubst (a,t) (Fun t1 t2) = Fun (tsubst (a,t) t1) (tsubst (a,t) t2)
tsubst (a,t) Ints = Ints

tsubstCon :: (TVars,Types) -> [Constr] -> [Constr]
tsubstCon (a,t) [] = []
tsubstCon (a,t) ((t1,t2):cs) = (tsubst (a,t) t1, tsubst (a,t) t2) : tsubstCon (a,t) cs
