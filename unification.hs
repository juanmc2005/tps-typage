------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
--------------------------------------- TP2 Ex3 Unification Algorithm --------------------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

import Data.List
import Data.Maybe

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
type EquationSystem = [Equation]

-- Definition of a mapping
type Mapping = (Int, Type)

-- Definition of a substitution: a set of variable to type pairs,
-- where the variable is represented as an Int (as in TVar Int)
type Substitution = [Mapping]


-- Unification algorithm
unify :: EquationSystem -> Maybe Substitution
unify eqs = let maybeSolution = toSubstitution eqs in
              if isJust maybeSolution then maybeSolution else let newEqs = eqSysUnificationStep eqs in
                if isJust newEqs then unify $ fromJust newEqs else Nothing

-- Perform a single step of unification with the first equation that allows for it in an equation system
eqSysUnificationStep :: EquationSystem -> Maybe EquationSystem
eqSysUnificationStep eqs = fromMaybe Nothing newEqs
                             where
                                unificationStep = \eq -> eqUnificationStep (delete eq eqs) eq
                                newEqs = find isJust $ map unificationStep eqs

-- Perform a step of the unification algorithm for an equation
eqUnificationStep :: EquationSystem -> Equation -> Maybe EquationSystem
eqUnificationStep eqs (t1, t2) = if t1 == t2 then Just eqs else applyUnificationRule eqs (t1, t2) -- Elimination

-- Apply a unification rule other than elimination
applyUnificationRule :: EquationSystem -> Equation -> Maybe EquationSystem
applyUnificationRule eqs (TVar v, s)                        = if eqSysHasVar v eqs && not (hasVar v s) -- Replacement
                                                                then Just $ (TVar v, s):(substituteEqSystem [(v, s)] eqs)
                                                                else Nothing
applyUnificationRule eqs (t, TVar v)                        = Just $ (TVar v, t):eqs             -- Exchange
applyUnificationRule eqs (TPair s1 s2, TPair t1 t2)         = Just $ [(s1, t1), (s2, t2)] ++ eqs -- Decomposition
applyUnificationRule eqs (TFunction s1 s2, TFunction t1 t2) = Just $ [(s1, t1), (s2, t2)] ++ eqs -- Decomposition
applyUnificationRule _   _                                  = Nothing

-- Checks if an equation system is in solved form
isSolved :: EquationSystem -> Bool
isSolved eqs = foldr (&&) True (map isSolvedForm eqs)

-- Checks if an equation is in solved form
isSolvedForm :: Equation -> Bool
isSolvedForm (TVar _, term) = vars term == 0
isSolvedForm _              = False

-- Transforms an equation system into a substitution
toSubstitution :: EquationSystem -> Maybe Substitution
toSubstitution eqs = if isSolved eqs then Just $ map (fromJust . toMapping) eqs else Nothing

-- Transforms an equation into a substitution
toMapping :: Equation -> Maybe Mapping
toMapping (TVar v, term) = Just (v, term)
toMapping _              = Nothing

-- Applies a substitution to an equation system
substituteEqSystem :: Substitution -> EquationSystem -> EquationSystem
substituteEqSystem sub eqs = map (substituteEquation sub) eqs

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

-- Checks if a variable is present in an equation system
eqSysHasVar :: Int -> EquationSystem -> Bool
eqSysHasVar v eqs = foldr (||) False $ map (eqHasVar v) eqs

-- Checks if a variable is present in an equation
eqHasVar :: Int -> Equation -> Bool
eqHasVar v (t1, t2) = hasVar v t1 || hasVar v t2

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

main = print $ unify eqs
         where 
            eqs = [(TVar 0, TVar 1), (TVar 2, TVar 3), (TVar 3, TInt), (TVar 4, TFunction (TInt) (TVar 1)), (TVar 1, TInt)]