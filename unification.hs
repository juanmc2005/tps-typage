------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
--------------------------------------- TP2 Ex3 Unification Algorithm --------------------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

-- Definition of a type
data Type = TInt | TBool | TVar Int | TPair Type Type | TFunction Type Type deriving (Eq, Ord)
instance Show Type where
    show TInt            = "Int"
    show TBool           = "Bool"
    show (TPair a b)     = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TFunction a b) = show a ++ " -> " ++ show b
    show (TVar v)        = "x" ++ show v

-- Definition of an equation
type Equation = (Type, Type)

-- Definition of an equation system
type EquationSystem = Set Equation

-- Definition of a substitution: a set of variable to type pairs,
-- where the variable is represented as an Int (as in TVar Int)
type Substitution = [(Int, Type)]


-- Unification algorithm
-- unify :: EquationSystem -> Maybe Substitution

-- Perform a step of the unification algorithm for an equation
unificationStep :: EquationSystem -> Equation -> EquationSystem
-- Exchange rule
unificationStep eqs (t, TVar v)                         = Set.insert (TVar v, t) eqs
-- Decomposition rule for pairs
unificationStep eqs (TPair s1 s2, TPair t1 t2)          = Set.union eqs $ Set.fromList [(s1, t1), (s2, t2)]
-- Decomposition rule for functions
unificationStep eqs (TFunction s1 s2, TFunction t1 t2)  = Set.union eqs $ Set.fromList [(s1, t1), (s2, t2)]
-- Replacement rule
unificationStep eqs (TVar v, s)                         = if not (hasVar v s)
                                                          then Set.insert (TVar v, s) $ substituteEqSystem [(v, s)] eqs
                                                          else Set.insert (TVar v, s) eqs
-- Elimination rule
unificationStep eqs (t1, t2)                            = if t1 == t2 then eqs else Set.insert (t1, t2) eqs

-- Checks if an equation system is in solved form
isSolved :: EquationSystem -> Bool
isSolved eqs = Set.foldr (&&) True (Set.map isSolvedForm eqs)

-- Checks if an equation is in solved form
isSolvedForm :: Equation -> Bool
isSolvedForm (TVar _, term) = vars term == 0
isSolvedForm _              = False

-- Applies a substitution to an equation system
substituteEqSystem :: Substitution -> EquationSystem -> EquationSystem
substituteEqSystem sub eqs = Set.map (substituteEquation sub) eqs

-- Applies a substitution to an equation
substituteEquation :: Substitution -> Equation -> Equation
substituteEquation sub (t1, t2) = (substituteTerm sub t1, substituteTerm sub t2)

-- Applies a substitution to a term (Type)
substituteTerm :: Substitution -> Type -> Type
substituteTerm sub TInt              = TInt
substituteTerm sub TBool             = TBool
substituteTerm sub (TVar v)          = fromMaybe (TVar v) (findTerm sub v)
substituteTerm sub (TPair t1 t2)     = TPair (substituteTerm sub t1) (substituteTerm sub t2)
substituteTerm sub (TFunction t1 t2) = TFunction (substituteTerm sub t1) (substituteTerm sub t2)

-- Find the term (Type) that substitutes a given variable (int) in a substitution
findTerm :: Substitution -> Int -> Maybe Type
findTerm sub v = fmap snd $ find (\x -> (fst x) == v) sub

-- Checks if a variable (Int as in TVar Int) appears in a term (Type)
hasVar :: Int -> Type -> Bool
hasVar _ TInt              = False
hasVar _ TBool             = False
hasVar v (TVar x)          = v == x
hasVar v (TPair t1 t2)     = hasVar v t1 || hasVar v t2
hasVar v (TFunction t1 t2) = hasVar v t1 || hasVar v t2

-- Count the variables in a term
vars :: Type -> Int
vars TBool             = 0
vars TInt              = 0
vars (TVar _)          = 1
vars (TPair t1 t2)     = vars t1 + vars t2
vars (TFunction t1 t2) = vars t1 + vars t2


---------------------------------------------------------------------------------------------------

main = print $ isSolved $ Set.fromList [(TVar 10, TFunction TInt TBool), ((TVar 2), TPair TInt TInt)]