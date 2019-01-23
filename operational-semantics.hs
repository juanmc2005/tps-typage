
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
---------------------------- Implementation of Operational Semantics Evaluation ----------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

-- Definition of a program, either a constant, a variable, a function application or a lambda definition
data Program = Const Int
             | Lambda Int Program
             | Fix Program
             | Applic Program Program
             | LetIn Int Program Program
             | IfElse Program Program Program
             deriving Show

-- Definition of a substitution
type Subst = [(Int, Program)]

-- Takes a program and returns whether it's a lazy form
isLazyForm :: Program -> Bool
isLazyForm (Const _)    = True
isLazyForm (Lambda _ _) = True
isLazyForm (Fix _)      = True
isLazyForm _            = False

-- Evaluates a program using call by name semantics. None is returned if there's no derivation possible
evalByName :: Program -> Maybe Program
evalByName prog = if isLazyForm prog then prog else reductionByName prog

-- Evaluates a program using call by name semantics and returns a lazy form (program)
-- Returns None if no derivation is possible
{- TODO
reductionByName :: Program -> Maybe Program
reductionByName (Applic (Lambda var L) N) = if isLambda p1 then 
-}

-- Applies a given substitution to a given expression
-- TODO
applysub :: Subst -> Program -> Program
applysub (Applic p1 p2) sub = Applic (applysub p1 sub) (applysub p2 sub)
applysub (Lambda v e)   sub = Lambda v $ applysub e $ filter (\p -> (fst p) /= v) sub
applysub (Var v)        sub = if isJust repl then fromJust repl else Var v
                            where repl = findExpr sub v

-----------------------------------------------------------------


main = print "Hello!"