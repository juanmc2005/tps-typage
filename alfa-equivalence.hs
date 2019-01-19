import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

-------------------- Type Definitions --------------------

-- Definition of an expression, either a variable, a function application or a lambda definition
data Expr = Var Char | Applic Expr Expr | Lambda Char Expr deriving Show
-- Definition of a substitution
type Subst = [(Char, Expr)]
-- Definition of a name to name substitution
type Renaming = [(Char, Char)]

----------------------------------------------------------

--------------------- Main Functions ---------------------

-- Checks if 2 given expressions are alfa equivalent
alfaeq :: Expr -> Expr -> Bool
alfaeq (Var n1)         (Var n2)         = n1 == n2
alfaeq (Applic e1 e2)   (Applic e3 e4)   = alfaeq e1 e3 && alfaeq e2 e4
alfaeq (Lambda v1 exp1) (Lambda v2 exp2) = alfaeq (applysub exp1 [(v1, freshvar)]) (applysub exp2 [(v2, freshvar)])
                                         where freshvar = Var $ head $ (fresh exp1) `intersect` (fresh exp2)
alfaeq _                _                = False

-- Returns an expression alfaequivalent to a given expression
genAlfaeq :: Expr -> Expr
genAlfaeq exp = rename exp [(name1, repl1), (name2, repl2)]
              where
               names = Set.toList $ bound exp
               repls = fresh exp
               name1 = head names
               name2 = head $ tail names
               repl1 = head repls
               repl2 = head $ tail repls

----------------------------------------------------------

--------------------- Other Functions --------------------

-- The character list corresponding to the alfabet (possible variable names)
alfabet :: String
alfabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

-- Applies a given substitution to a given expression
applysub :: Expr -> Subst -> Expr
applysub (Applic e1 e2) sub = Applic (applysub e1 sub) (applysub e2 sub)
applysub (Lambda v e)   sub = Lambda v $ applysub e $ filter (\p -> (fst p) /= v) sub
applysub (Var v)        sub = if isJust repl then fromJust repl else Var v
                            where repl = findExpr sub v

-- Rename all bound variables in an expression according to a Renaming scheme (list of char-char pairs)
rename :: Expr -> Renaming -> Expr
rename (Var v) ren        = Var v
rename (Applic e1 e2) ren = Applic (rename e1 ren) (rename e2 ren)
rename (Lambda v exp) ren = Lambda newName $ rename (applysub exp [(v, Var newName)]) ren
                          where
                           maybeNewName = fmap snd $ find (\p -> (fst p) == v) ren
                           newName = if isJust maybeNewName then fromJust maybeNewName else v

-- Find the expression that substitutes a given character in a substitution
findExpr :: Subst -> Char -> Maybe Expr
findExpr sub v = fmap snd $ find (\x -> (fst x) == v) sub

-- Returns a list of fresh variable names (characters) for a given expression
fresh :: Expr -> [Char]
fresh e = alfabet \\ Set.toList (vars e)

-- Returns all variable names present in a given expression, either bound or unbound
vars :: Expr -> Set Char
vars exp = Set.union (bound exp) (unbound exp)

-- Returns all bound variable names in a given expression
bound :: Expr -> Set Char
bound (Var c)        = Set.empty
bound (Applic e1 e2) = Set.union (bound e1) (bound e2)
bound (Lambda c exp) = Set.union (Set.singleton c) (bound exp)

-- Returns all unbound variable names in a given expression
unbound :: Expr -> Set Char
unbound (Var c)        = Set.singleton c
unbound (Applic e1 e2) = Set.union (unbound e1) (unbound e2)
unbound (Lambda c exp) = Set.delete c $ unbound exp

----------------------------------------------------------


main = print $ alfaeq exp1 $ genAlfaeq exp1
    where
     exp1 = Lambda 'x' $ Applic (Lambda 'y' $ Applic (Var 'z') (Var 'y')) (Var 'x')
