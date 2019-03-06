------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
----------------------------------------------- Unification ------------------------------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

module JMTypesRec (
    Type(TInt, TBool, TVar, TPair, TFunction, TRec),
    Equation, EquationSystem, Mapping, Substitution,
    unify, isSolved, isSolvedForm, eqSysUnificationStep, typesEqual, eqSysHasVar) where

import Data.List
import Data.Maybe

-- Definition of a type
data Type = TInt | TBool | TVar Int | TPair Type Type | TFunction Type Type | TRec Int Type deriving (Eq, Ord)
instance Show Type where
    show TInt            = "Int"
    show TBool           = "Bool"
    show (TPair a b)     = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TFunction a b) = show a ++ " -> " ++ show b
    show (TVar v)        = "t" ++ show v
    show (TRec v a)      = "µt" ++ show v ++ ".(" ++ show a ++ ")"

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
applyUnificationRule eqs (TVar v, s)                        = if eqSysHasVar v eqs then -- Replacement
                                                                if not (isRecursive s) then
                                                                  if hasVar v s then Just $ (TVar v, TRec v s):eqs
                                                                  else Just $ (TVar v, s):(substituteEqSystem [(v, s)] eqs)
                                                                else Just $ substituteEqSystem [(v, s)] eqs
                                                              else Nothing
applyUnificationRule eqs (t, TVar v)                        = Just $ (TVar v, t):eqs             -- Exchange
applyUnificationRule eqs (TPair s1 s2, TPair t1 t2)         = Just $ [(s1, t1), (s2, t2)] ++ eqs -- Decomposition
applyUnificationRule eqs (TFunction s1 s2, TFunction t1 t2) = Just $ [(s1, t1), (s2, t2)] ++ eqs -- Decomposition
applyUnificationRule eqs (TRec x1 t, TRec x2 s)             = if typesEqual (TRec x1 t) (TRec x2 s) then Just eqs else Nothing
applyUnificationRule eqs (TRec x t, s)                      = applyUnificationRule eqs (unroll (TRec x t), s)
applyUnificationRule eqs (t, TRec x s)                      = applyUnificationRule eqs (t, unroll (TRec x s))
applyUnificationRule _   _                                  = Nothing

-- Checks if an equation system is in solved form
isSolved :: EquationSystem -> Bool
isSolved eqs = if areAllLeftVars eqs then noTermHasVars vars terms else False
               where
                 vars = map (varId . fst) eqs
                 terms = map snd eqs

-- Checks if all left sides of an equation system are var types
areAllLeftVars :: EquationSystem -> Bool
areAllLeftVars eqs = foldr (&&) True $ map (isVar . fst) eqs

-- Checks if no type variables from a given list appear in a list of types
noTermHasVars :: [Int] -> [Type] -> Bool
noTermHasVars (v:vs) ts = (noTermHasVar v ts) && (noTermHasVars vs ts)
noTermHasVars [] _ = True

-- Checks if no type in a list of types contains a given variable
noTermHasVar :: Int -> [Type] -> Bool
noTermHasVar v ts = not (someTermHasVar v ts)

-- Checks if a type in a list of types contains a type variable
someTermHasVar :: Int -> [Type] -> Bool
someTermHasVar v ts = foldr (||) False (map (hasVar v) ts)

-- Checks if an equation is in solved form
isSolvedForm :: Equation -> Bool
isSolvedForm (TVar v, term)     = not (hasVar v term)
isSolvedForm _                  = False

-- Transforms an equation system into a substitution
toSubstitution :: EquationSystem -> Maybe Substitution
toSubstitution eqs = if isSolved eqs then Just $ map (fromJust . toMapping) eqs else Nothing

-- Transforms an equation into a substitution mapping
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
substituteTerm sub (TRec v t)        = if isJust $ findTerm sub v then TRec v t else TRec v (substituteTerm sub t)

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
hasVar v (TRec tv t)       = if v /= tv then hasVar v t else False 

-- Count the variables in a term
vars :: Type -> Int
vars t = snd $ varsRec [] t

-- Count the variables in a term
varsRec :: [Int] -> Type -> ([Int], Int)
varsRec seen TBool             = (seen, 0)
varsRec seen TInt              = (seen, 0)
varsRec seen (TVar v)          = if elem v seen then (seen, 0) else (v:seen, 1)
varsRec seen (TPair t1 t2)     = (fst res2, snd res1 + snd res2)
                                 where
                                   res1 = varsRec seen t1
                                   res2 = varsRec (fst res1) t2
varsRec seen (TFunction t1 t2) = (fst res2, snd res1 + snd res2)
                                 where
                                   res1 = varsRec seen t1
                                   res2 = varsRec (fst res1) t2
varsRec seen (TRec v t)        = varsRec (v:seen) t

-- Check if a type is recursive
isRecursive :: Type -> Bool
isRecursive (TRec _ _) = True
isRecursive _          = False

-- Check if a type is a type variable
isVar :: Type -> Bool
isVar (TVar _) = True
isVar _ = False

-- Get id for a TVar
varId :: Type -> Int
varId (TVar x) = x
varId _ = error "Can't get the identifier of a non var type"

-- One step unroll a recursive type
unroll :: Type -> Type
unroll (TRec x t) = substituteTerm [(x, TRec x t)] t
unroll t          = t

typesEqual :: Type -> Type -> Bool
typesEqual t1 t2 = (leftEquals [(t1, t2)] t1 t2) && (leftEquals [(t2, t1)] t2 t1)

-- Check if two types are equal according to the coinductive definition
leftEquals :: EquationSystem -> Type -> Type -> Bool
leftEquals rel TBool TBool                         = True
leftEquals rel TInt TInt                           = True
leftEquals rel (TPair a1 a2) (TPair b1 b2)         = if not $ elem (a1, b1) rel then
                                                       if not $ elem (a2, b2) rel then
                                                         (leftEquals fullrel a1 b1) && (leftEquals fullrel a2 b2)
                                                       else leftEquals ((a1, b1):rel) a1 b1
                                                     else leftEquals ((a2, b2):rel) a2 b2
                                                     where
                                                       fullrel = (a1, b1):(a2, b2):rel
leftEquals rel (TFunction a1 a2) (TFunction b1 b2) = if not $ elem (b1, a1) rel then
                                                       if not $ elem (a2, b2) rel then
                                                         (leftEquals fullrel b1 a1) && (leftEquals fullrel a2 b2)
                                                       else leftEquals ((b1, a1):rel) b1 a1
                                                     else leftEquals ((a2, b2):rel) a2 b2
                                                     where
                                                       fullrel = (b1, a1):(a2, b2):rel
leftEquals rel a (TRec x b)                        = if not $ elem (a, unrolled) rel then
                                                       leftEquals ((a, unrolled):rel) a unrolled
                                                     else True
                                                     where
                                                       unrolled = unroll (TRec x b)
leftEquals rel (TRec x a) b                        = if not $ elem (unrolled, b) rel then
                                                       leftEquals ((unrolled, b):rel) unrolled b
                                                     else True
                                                     where
                                                       unrolled = unroll (TRec x a)
leftEquals _ _ _                                   = False