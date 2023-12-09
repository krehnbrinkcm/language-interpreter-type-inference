-- Part 2. Reduction

allVars :: [Vars]
allVars = ("" : allVars) >>= (\s -> (map (\x -> s ++ [x]) ['a'..'z']))

freshVar :: [Vars] -> Vars
freshVar xs = allVars !! (maximum (catMaybes [elemIndex x allVars | x <- xs]) + 1)

fv :: Terms -> [Vars]
fv (Var x) = [x]
fv (Abs x r) = filter (/= x) (fv r)
fv (App s t) = nub $ fv s ++ fv t
fv (Sub s t) = nub $ fv s ++ fv t
fv (IfPos r s t) = nub $ fv r ++ fv s ++ fv t  -- change to if
-- Add
-- fpc 
-- succ
-- leq
-- Rec
-- pair ?
-- fst ?
-- snd ?
fv _ = []


--ALL ELSE HAS NOT BEEN CHECKED

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
