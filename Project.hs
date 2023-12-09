import Data.Char (isAlphaNum,isSpace,isDigit,isLower)
import Data.List (isPrefixOf,elemIndex,nub)
import Data.Maybe (catMaybes)

-- Haskell Representation of PCF Syntax

type Vars = String
type TVars = String

data Types = Int | Bool | Unit | Fun Types Types | Prod Types Types | TVar TVars deriving Show

data Terms = Var Vars| App Terms Terms | Abs Vars Terms
           | Const Integer | Add Terms Terms | Sub Terms Terms 
           | Leq Terms Terms | Rec Terms Terms Terms | S Terms
           | TT | FF | If Terms Terms Terms | Pair Terms Terms 
           | Fst Terms | Snd Terms | Fpc Terms
           deriving (Show,Eq)

data Token = VSym String | CSym Integer 
           | SubOp | AddOp | LeqOp | TrueK | FalseK | IfK | ThenK | ElseK
           | PairK | FstK | SndK | RecK | YComb | ZeroK | SuccK
           | LPar | RPar | Comma | Dot | Backslash | UnitK
           | Err String | PT Terms
           deriving (Eq,Show)

--Parsing and Lexical Analysis 
lexer :: String -> [Token]
lexer ('+':s)                   = AddOp : lexer s 
lexer ('-':s)                   = SubOp : lexer s
lexer ('Y':s)                   = YComb : lexer s
lexer ('S':s)                   = SuccK : lexer s
lexer ('<':'=':s)               = LeqOp : lexer s
lexer s | isPrefixOf "pair" s   = PairK : lexer (drop 4 s)
lexer s | isPrefixOf "fst" s    = FstK : lexer (drop 3 s)
lexer s | isPrefixOf "snd" s    = SndK : lexer (drop 3 s)
lexer s | isPrefixOf "rec" s    = RecK : lexer (drop 3 s)
lexer s | isPrefixOf "if" s     = IfK : lexer (drop 2 s)
lexer s | isPrefixOf "then" s   = ThenK : lexer (drop 4 s)
lexer s | isPrefixOf "else" s   = ElseK : lexer (drop 4 s)
lexer ('0':s)                   = ZeroK : lexer s
lexer ('(':s)                   = LPar : lexer s
lexer (')':s)                   = RPar : lexer s
lexer ('.':s)                   = Dot : lexer s
lexer (',':s)                   = Comma : lexer s
lexer ('1':s)                   = UnitK : lexer s
lexer ('\\':s)                  = Backslash : lexer s 
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
sr (CSym n : ts) i                                          = sr (PT (Const n) : ts) i
sr (ZeroK : ts) i                                           = sr (PT (Const 0) : ts) i
sr (UnitK : ts) i                                           = sr (PT (Const 1) : ts) i 
sr (VSym n : ts) i                                          = sr (PT (Var n) : ts) i
sr (TrueK : ts) i                                           = sr (PT (TT) : ts) i
sr (FalseK : ts) i                                          = sr (PT (FF) : ts) i
sr (PT t1 : YComb : ts) i                                   = sr (PT (Fpc t1): ts) i
sr (PT n : SuccK : ts) i                                    = sr (PT (S n) : ts) i -- might not work
sr (PT n : PT f : PT z : RecK : ts) i                       = sr (PT (Rec z f n) : ts) i
sr (PT t2 : PT t1 : LeqOp : ts) i                           = sr (PT (Leq t1 t2) : ts) i
sr (PT t3 : ElseK : PT t2 : ThenK : PT t1 : IfK : ts) i     = sr (PT (If t1 t2 t3) : ts) i
sr (PT t2 : Comma : PT t1 : PairK : ts) i                   = sr (PT (Pair t1 t2) : ts) i
sr (PT t2 : Comma : PT t1 : FstK : ts) i                    = sr (PT (Fst (Pair t1 t2)) : ts) i -- might not work
sr (PT t2 : Comma : PT t1 : SndK : ts) i                    = sr (PT (Snd (Pair t1 t2)) : ts) i -- might not work
sr (PT t2 : AddOp : PT t1 : ts) i                           = sr(PT(Add t1 t2) : ts) i 
sr (PT t2 : SubOp : PT t1 : ts) i                           = sr(PT(Sub t1 t2) : ts) i 
sr (RPar : PT t : LPar : ts) i                              = sr (PT t : ts) i
sr (PT r : Dot : PT (Var x) : Backslash : ts) i             = sr (PT (Abs x r) : ts) i
sr (PT t2 : PT t1 : ts) i                                   = sr (PT (App t1 t2) : ts) i
sr m (i0:i)                                                 = sr (i0:m) i
sr st []                                                    = st