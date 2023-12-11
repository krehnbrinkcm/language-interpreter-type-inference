-- Project 
import Data.Char
import Data.List
import Data.Maybe


type Vars = String;
type TVars = String;


data Types = TVar TVars | Fun Types Types | Prod Types Types


data Terms = Var Vars | App Terms Terms | Abs Vars Terms 
    | Zero | Succ Terms | Rec Terms Terms Terms | Pair Terms Terms 
    | Fst Terms | Snd Terms
    deriving (Show,Eq)


data Token = VSym Vars | LPar | RPar | Dot | Backslash |
        Err String | ZeroK | SK | RecK | CommaK | FstK | SndK | PT Terms
    deriving (Show)


lexer :: String -> [Token]
lexer "" = []
lexer ('.':s) = (Dot : lexer s)
lexer ('\\':s) = (Backslash : lexer s)
lexer (',':s) = (CommaK : lexer s)
lexer ('(':s) = (LPar : lexer s)
lexer (')':s) = (RPar : lexer s)
lexer ('S':s) = (SK : lexer s)
lexer s | isPrefixOf "zero" s  = ZeroK : lexer (drop 4 s)
lexer s | isPrefixOf "fst" s  = FstK : lexer (drop 3 s)
lexer s | isPrefixOf "snd" s  = SndK : lexer (drop 3 s)
lexer s | isPrefixOf "recursion" s  = ZeroK : lexer (drop 4 s)                  -- maybe change string representation
lexer (c:s) | isLower c = let (var,rst) = span isAlphaNum s
                            in (VSym (c:var) : lexer rst)
lexer (c:s) | isSpace c = lexer s
lexer (c:s) = (Err ("Invalid character " ++ [c]) : lexer s)                     -- could make lexical errors print better


parser :: [Token] -> Either Terms String
parser ts = case sr [] ts of
  [PT t]  -> Left t
  []      -> Right ""
  [Err e] -> Right e
  st      -> Right $ "Parse error: " ++ show st


sr :: [Token] -> [Token] -> [Token]
sr (VSym x : s)                              q = sr (PT (Var x)     : s) q
sr (ZeroK : s)                              q = sr (PT (Zero)     : s) q
sr (PT e3 : PT e2 : PT e1 : RecK : s) q = sr (PT (Rec e1 e2 e3) : s) q
sr (PT e2 : PT e1 : s)                       q = sr (PT (App e1 e2) : s) q
sr (PT e2 : CommaK : PT e1 : s)                       q = sr (PT (Pair e1 e2) : s) q
sr (PT e1 : FstK : s)                       q = sr (PT (Fst e1) : s) q
sr (PT e1 : SndK : s)                       q = sr (PT (Snd e1) : s) q
sr (PT e1 : Dot : PT (Var x) : Backslash : s)  q = sr (PT (Abs x e1)  : s) q
sr (PT e1 : SK : s)               q = sr (PT (Succ e1) : s) q
sr (RPar : PT e1 : LPar : s)                     q = sr (PT e1 : s) q
sr (Err e : ts) i = [Err e]
sr st      (i:is) = sr (i:st) is
sr st          [] = st


subst :: (Vars,Terms) -> Terms -> Terms
subst (v,t) (Succ e1) = Succ (subst (v,t) e1)
subst (v,t) (Zero) = Zero
subst (v,t) (Var x) = if x == v then t else (Var x)
subst (v,t) (App e1 e2) = App (subst (v,t) e1) (subst (v,t) e2)
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


allVars :: [String]
allVars = "" : newVars
  where newVars = allVars >>= (\var -> [ var ++ [l] | l <- ['a'..'z']])

freshVar :: [String] -> String
freshVar vs =
  let inds = catMaybes (map (\x -> elemIndex x allVars) ("":vs))
   in allVars !! (maximum inds + 1)

fv :: Terms -> [Vars]
fv (Var x) = [x]
fv (App s t) = nub $ fv s ++ fv t
fv (Abs x t) = filter (/= x) (fv t)


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
           

type Constr = (Types,Types)
type Context = [(Vars,Types)]
type TSub = [(TVars,Types)]


tsubst :: (TVars,Types) -> Types -> Types
tsubst (a,t) (TVar b) | a == b = t
                    | otherwise = TVar b
tsubst (a,t) (Fun t1 t2)  = Fun (tsubst (a,t) t1) (tsubst (a,t) t2 )
tsubst (a,t) (Prod t1 t2)  = Prod (tsubst (a,t) t1) (tsubst (a,t) t2 )


tsubstCon :: (TVars,Types) -> [Constr] -> [Constr]
tsubstCon (a,t) [] = []
tsubstCon (a,t) ((t1,t2):cs) = (tsubst (a,t) t1, tsubst (a,t) t2) : tsubstCon (a,t) cs


ftv :: Types -> [TVars]
ftv (TVar a) = [a]
ftv (Fun t1 t2) = ftv t1 ++ ftv t2
ftv (Prod t1 t2) = ftv t1 ++ ftv t2


ftvC :: Context -> [TVars]
ftvC [] = []
ftvC ((x,a) : g) = ftv a ++ ftvC g


genConstr :: Context -> Terms -> Types -> [Constr]                 -- need to implement rest of rules
genConstr g (Var x) a = case lookup x g of
                          Just b  -> [(a,b)]
                          Nothing -> error "Variable not found in context"
genConstr g (App s t) b =
  let a = freshVar (ftv b ++ ftvC g)
      c1 = genConstr g s (Fun (TVar a) b)
      c2 = genConstr g t (TVar a)
   in c1 ++ c2
genConstr g (Abs x r) b =
  let a1 = freshVar (ftv b ++ ftvC g)
      a2 = freshVar (a1 : (ftv b ++ ftvC g))
   in (b , Fun (TVar a1) (TVar a2)) : genConstr ((x,TVar a1):g) (r) (TVar a2)








