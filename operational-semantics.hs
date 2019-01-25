
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
---------------------------- Implementation of Operational Semantics Evaluation ----------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

import Data.Maybe
import Data.List

-- Definition of a program
data Program = Const Int
             | Var Int
             | Lambda Int Program
             | Fix Program
             | Applic Program Program
             | LetIn Int Program Program
             | IfElse Program Program Program
             deriving Show

true  = -2
false = -1

-- Definition of a substitution
type Subst = [(Int, Program)]

-- Takes a program and returns whether it's a lazy form
isLazyForm :: Program -> Bool
isLazyForm (Const _)    = True
isLazyForm (Var _)      = True -- ?? What to do avec variables?
isLazyForm (Lambda _ _) = True
isLazyForm (Fix _)      = True
isLazyForm _            = False

-- Evaluates a program using call by name semantics. None is returned if there's no derivation possible
evalByName :: Program -> Maybe Program
evalByName prog = if isLazyForm prog then Just prog else reductionByName prog

-- Evaluates a program using call by name semantics and returns a lazy form (program)
-- Returns None if no derivation is possible
reductionByName :: Program -> Maybe Program
reductionByName (Applic (Lambda var m) n) = evalByName $ substitute [(var, n)] m
reductionByName (Applic (Fix m) n)        = evalByName (Applic (Applic m (Fix m)) n)
reductionByName (Applic m n)              = if isJust mEval
                                            then reductionByName $ Applic (fromJust mEval) n
                                            else Nothing
                                          where mEval = reductionByName m
reductionByName (LetIn x m l)             = evalByName $ substitute [(x, m)] l
reductionByName (IfElse (Const (-2)) n l) = evalByName n
reductionByName (IfElse (Const (-1)) n l) = evalByName l
reductionByName (IfElse expr n l)         = if isJust cond
                                            then evalByName $ IfElse (fromJust cond) n l
                                            else Nothing
                                          where cond = evalByName expr
reductionByName _                         = Nothing

-- Applies a given substitution to a given expression
substitute :: Subst -> Program -> Program
substitute sub (Applic p1 p2)    = Applic (substitute sub p1) (substitute sub p2)
substitute sub (Lambda v p)      = Lambda v $ substitute (filter (\p -> (fst p) /= v) sub) p
substitute sub (Fix p)           = Fix $ substitute sub p
substitute sub (Const c)         = Const c
substitute sub (LetIn v p1 p2)   = LetIn v (substitute sub p1) (substitute subWithoutV p2)
                                 where subWithoutV = filter (\p -> (fst p) /= v) sub
substitute sub (IfElse p1 p2 p3) = IfElse (substitute sub p1) (substitute sub p2) (substitute sub p3)
substitute sub (Var v)           = if isJust repl then fromJust repl else Var v
                                 where repl = findProg sub v

-- Find the expression that substitutes a given character in a substitution
findProg :: Subst -> Int -> Maybe Program
findProg sub v = fmap snd $ find (\x -> (fst x) == v) sub

-----------------------------------------------------------------


main = print $ evalByName (Applic (Applic m n) (Lambda 27 n))
     where
        m = Lambda 2 (Lambda 3 (Applic (Var 2) (Var 3)))
        n = Lambda 4 $ Var 4

-- main = print $ substitute [(2, Lambda 4 (Var 4))] (Lambda 3 (Applic (Var 2) (Var 3)))