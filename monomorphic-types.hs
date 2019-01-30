------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
----------------------------------- TP2 Ex2 Monomorphic Typing Algorithm -----------------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import qualified Data.Map as Map

-- Definition of a program
data Program = Const Int
             | Var Int
             | Pair Program Program
             | Lambda Int Type Program
             | Fix Program
             | Applic Program Program
             | LetIn Int Type Program Program
             | IfElse Program Program Program
             deriving Show

-- Definition of a type
data Type = TInt | TBool | TPair Type Type | TFunction Type Type deriving (Show, Eq)

-- Type alias for a type environment: a map from variables (int codes, as in Var Int) to types
type TypeEnv = Map.Map Int Type

true  = -2
false = -1

-- Calculate the type of a given program in a given type environment
ptype :: TypeEnv -> Program -> Maybe Type
ptype _   (Const c)           = Just (consttype c)
ptype env (Var v)             = Map.lookup v env
ptype env (Applic m n)        = do { mtype <- ptype env m ; ntype <- ptype env n ; applictype mtype ntype }
ptype env (Lambda v vtype m)  = let newenv = Map.insert v vtype env in
                                do { mtype <- ptype newenv m ; Just $ TFunction vtype mtype }
ptype env (Pair m n)          = do { mtype <- ptype env m ; ntype <- ptype env n ; Just $ TPair mtype ntype }
ptype env (LetIn v vtype m n) = let newenv = Map.insert v vtype env in
                                do { mtype <- ptype env m ; ntype <- ptype newenv n ; letintype vtype mtype ntype }
ptype env (Fix m)             = do { mtype <- ptype env m ; fixtype mtype }
-- TODO if else

-- Calculate the type of a given constant (int code, as in Const Int)
consttype :: Int -> Type
consttype -2 = TBool
consttype -1 = TBool
consttype _  = TInt

-- Calculate the type of an application given the types of the left and right side terms
applictype :: Type -> Type -> Maybe Type
applictype (TFunction a b) c = if c == a then Just b else Nothing
applictype _               _ = Nothing

-- Calculate the type of a 'let in' expression given the types of
-- the declared variable, the assignment and the body
letintype :: Type -> Type -> Type -> Maybe Type
letintype vtype mtype ntype = if vtype == mtype then Just ntype else Nothing

-- Calculate the type of a fix expression given the type of the expression fix is applied to
fixtype :: Type -> Maybe Type
fixtype (TFunction a b) = Just a
fixtype _               = Nothing


main = print "Unfinished"
