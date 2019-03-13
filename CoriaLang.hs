module CoriaLang where

import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

----------------------------------------- Language Types -----------------------------------------
-- Definition of a type
data Type = TInt | TBool | TVar Int | TPair Type Type | TFunction Type Type | TRec Int Type deriving (Eq, Ord)
instance Show Type where
    show TInt            = "Int"
    show TBool           = "Bool"
    show (TPair a b)     = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (TFunction a b) = show a ++ " -> " ++ show b
    show (TVar v)        = "t" ++ show v
    show (TRec v a)      = "µt" ++ show v ++ ".(" ++ show a ++ ")"

-- Definition of a polymorphic type
data PolyType = ForEvery [Int] Type deriving Eq
instance Show PolyType where
    show (ForEvery (v:vs) t) = "∀t" ++ show v ++ "." ++ show (ForEvery vs t)
    show (ForEvery [] t)     = show t

-- Definition of an equation
type Equation = (Type, Type)
-- Definition of an equation system
type EquationSystem = [Equation]
-- Definition of a mapping
type Mapping = (Int, Type)
-- Definition of a substitution: a set of variable to type pairs,
-- where the variable is represented as an Int (as in TVar Int)
type Substitution = [Mapping]
--------------------------------------------------------------------------------------------------

-------------------------------------- Language Definition ---------------------------------------
-- Definition of a program
data Program = Const Int
             | Var Int
             | Pair Program Program
             | Lambda Int Program
             | Applic Program Program
             | LetIn Int Program Program
             deriving Show

-- Definition of a "variable to type variable" mapping
type TVarMapping = (Int, Int)
-- Definition of a type variable memory:
--   a number representing the next fresh variable to use
--   a set representing the current type var mappings
type TypeVarMem = (Int, Set TVarMapping)

-- Language constants
false = Const (-1)
true = Const (-2)
and' = Const (-3)
isZero = Const (-4)
--------------------------------------------------------------------------------------------------

-------------------------------------- Secondary Functions ---------------------------------------
-- Type a constant
constType :: Int -> Type
constType (-4) = TFunction TInt TBool
constType (-3) = TFunction (TPair TBool TBool) TBool
constType (-2) = TBool
constType (-1) = TBool
constType _    = TInt

-- Find the second element of a pair with a given first element in a foldable of pairs
flookup :: (Eq a, Foldable f) => a -> f (a, b) -> Maybe b
flookup k pairs = fmap snd $ find (\x -> (fst x) == k) pairs

-- Perform n steps of the unification algorithm (useful for debugging)
unifyN :: Int -> EquationSystem -> EquationSystem
unifyN n eqs = if n == 0 then eqs else unifyN (n-1) $ fromMaybe [] $ eqSysUnificationStep eqs

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

-- Find the term (Type) that substitutes a given variable (Int) in a substitution
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

-- Check if a type is recursive
isRecursive :: Type -> Bool
isRecursive (TRec _ _) = True
isRecursive _          = False

-- Check if a type is a type variable
isVar :: Type -> Bool
isVar (TVar _) = True
isVar _        = False

-- Get id for a TVar
varId :: Type -> Int
varId (TVar x) = x
varId _ = error "Can't get the identifier of a non var type"

-- Get free variables in a type given a list of variables to ignore
freeVarsIgnoring :: [Int] -> Type -> Set Int
freeVarsIgnoring _ TInt               = Set.empty
freeVarsIgnoring _ TBool              = Set.empty
freeVarsIgnoring vs (TVar v)          = if not (elem v vs) then Set.singleton v else Set.empty
freeVarsIgnoring vs (TPair t1 t2)     = Set.union (freeVarsIgnoring vs t1) (freeVarsIgnoring vs t2)
freeVarsIgnoring vs (TFunction t1 t2) = Set.union (freeVarsIgnoring vs t1) (freeVarsIgnoring vs t2)
freeVarsIgnoring vs (TRec v t)        = freeVarsIgnoring (v:vs) t

-- Get free variables in a type
freeVars :: Type -> Set Int
freeVars t = freeVarsIgnoring [] t

-- One step unroll a recursive type
unroll :: Type -> Type
unroll (TRec x t) = substituteTerm [(x, TRec x t)] t
unroll t          = t

-- Check if two types are equal according to the coinductive definition saw in class
typesEqual :: Type -> Type -> Bool
typesEqual t1 t2 = (leftEquals [(t1, t2)] t1 t2) && (leftEquals [(t2, t1)] t2 t1)

-- Check if a type is less or equal than another type according to the coinductive definition saw in class
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
leftEquals rel (TVar x) (TVar y)                   = x == y
leftEquals _ _ _                                   = False
--------------------------------------------------------------------------------------------------

---------------------------------------- Main Functions ------------------------------------------
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

-- Transform a program into its corresponding equation system
toEquationSystem :: Program -> EquationSystem
toEquationSystem prog = snd $ toEquationSystemRec (0, Set.empty) prog

-- Given a starting variable number and an initial mapping from vars to type vars,
-- transform a program into a type equation system with the mapping used during the transformation
toEquationSystemRec :: TypeVarMem -> Program -> (TypeVarMem, EquationSystem)
toEquationSystemRec (n, mem) (Const c)    = ((n+1, mem), [(TVar n, constType c)])
toEquationSystemRec (n, mem) (Var v)      = let maybeTvar = flookup v mem in
                                              if isJust maybeTvar
                                              then ((n+1, mem), [(TVar n, TVar (fromJust maybeTvar))])
                                              else ((n+2, mem), [(TVar n, TVar (n+1))])
toEquationSystemRec (n, mem) (Pair p1 p2) = ((vp2+1, Set.unions [mem, mem1, mem2]), [(TVar n, TPair (TVar vp1) (TVar vp2))] ++ snd p1Res ++ snd p2Res)
                                            where
                                              vp1 = n + 1
                                              p1Res = toEquationSystemRec (vp1, mem) p1
                                              state1 = fst p1Res
                                              vp2 = fst state1
                                              p2Res = toEquationSystemRec (vp2, mem) p2
                                              state2 = fst p2Res
                                              mem1 = snd state1
                                              mem2 = snd state2
toEquationSystemRec (n, mem) (Lambda v p) = (fst pRes, [(TVar n, TFunction (TVar vv) (TVar vp))] ++ snd pRes)
                                            where
                                              vv = n + 1
                                              vp = n + 2
                                              newMem = Set.insert (v, vv) mem
                                              pRes = toEquationSystemRec (vp, newMem) p
toEquationSystemRec (n, mem) (Applic p1 p2) = ((vp2+1, Set.unions [mem, mem1, mem2]), [(TVar vp1, TFunction (TVar vp2) (TVar n))] ++ snd p1Res ++ snd p2Res)
                                              where
                                                vp1 = n + 1
                                                p1Res = toEquationSystemRec (vp1, mem) p1
                                                state1 = fst p1Res
                                                vp2 = fst state1
                                                p2Res = toEquationSystemRec (vp2, mem) p2
                                                state2 = fst p2Res
                                                mem1 = snd state1
                                                mem2 = snd state2
toEquationSystemRec (n, mem) (LetIn x p1 p2) = ((vp2+1, Set.unions [mem, mem1, mem2]), [(TVar n, TVar vp2), (TVar vx, TVar vp1)] ++ snd p1Res ++ snd p2Res)
                                               where
                                                 vx = n + 1
                                                 vp1 = n + 2
                                                 newMem = Set.insert (x, vx) mem
                                                 p1Res = toEquationSystemRec (vp1, newMem) p1
                                                 state1 = fst p1Res
                                                 vp2 = fst state1
                                                 p2Res = toEquationSystemRec (vp2, newMem) p2
                                                 state2 = fst p2Res
                                                 mem1 = snd state1
                                                 mem2 = snd state2

-- Get the monomorphic type of a program
monoType :: Program -> Maybe Type
monoType p = lookup 0 $ fromMaybe [] $ unify $ toEquationSystem p

-- Infer the polymorphic type of a program
typeProgram :: Program -> Maybe PolyType
typeProgram p = let mtype = monoType p in
                if isJust mtype then let t = fromJust mtype in Just $ ForEvery (Set.toList (freeVars t)) t
                else Nothing
--------------------------------------------------------------------------------------------------

---------------------------------------- Validation Code -----------------------------------------
-- λx . x x
omegacomb = Lambda 100 (Applic (Var 100) (Var 100))
-- λx . f (x x)
ycombBody = Lambda 201 (Applic (Var 200) (Applic (Var 201) (Var 201)))
-- λf . (λx . f (x x)) (λx . f (x x))
ycomb = Lambda 200 (Applic ycombBody ycombBody)
-- λx . λy . (x, y)
toPair = Lambda 50 (Lambda 51 (Pair (Var 50) (Var 51)))
-- λx . let a = isZero x in a
isZero2 = Lambda 50 (LetIn 51 (Applic isZero (Var 50)) (Var 51))

ex1 = Lambda 200 (Lambda 201 (Applic (Var 200) (Applic (Var 201) (Var 201))))

-- Some type constants to play around
a = TRec 50 (TFunction (TVar 50) (TVar 50))
aArrowA = TFunction a a

main = do
       putStr "Given A = µx.(x -> x), A == A -> A ? "
       print $ typesEqual a aArrowA
       putStr "Omega Combinator\t\t\thas type "
       print $ typeProgram omegacomb
       putStr "Y Combinator\t\t\t\thas type "
       print $ typeProgram ycomb
       putStr "λx.λy.(x, y)\t\t\t\thas type "
       print $ typeProgram toPair
       putStr "λx.let a = isZero x in a\thas type "
       print $ typeProgram isZero2
--------------------------------------------------------------------------------------------------