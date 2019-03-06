module JMLang where

import JMTypesRec
import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

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

toEquationSystem :: Program -> EquationSystem
toEquationSystem prog = snd $ toEquationSystemRec (0, Set.empty) prog

-- Given a starting variable number and an initial mapping from vars to type vars,
-- transform a program into a type equation system with the mapping used during the transformation
toEquationSystemRec :: TypeVarMem -> Program -> (TypeVarMem, EquationSystem)
toEquationSystemRec (n, mem) (Const c)    = ((n+1, mem), [(TVar n, constType c)])
toEquationSystemRec (n, mem) (Var v)      = let maybeTvar = findSnd v mem in
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

-- Find the second element of a pair with a given first element in a list of pairs
findSnd :: (Eq a, Foldable f) => a -> f (a, b) -> Maybe b
findSnd k pairs = fmap snd $ find (\x -> (fst x) == k) pairs

-- Type a constant
constType :: Int -> Type
constType (-4) = TFunction TInt TBool
constType (-3) = TFunction (TPair TBool TBool) TBool
constType (-2) = TBool
constType (-1) = TBool
constType _    = TInt


-------------------------------------------------------------

unifyN :: Int -> EquationSystem -> EquationSystem
unifyN n eqs = if n == 0 then eqs else unifyN (n-1) $ fromMaybe [] $ eqSysUnificationStep eqs

false = Const (-1)
true = Const (-2)
andAnd = Const (-3)
isZero = Const (-4)

-- λx . x x
omegacomb = Lambda 100 (Applic (Var 100) (Var 100))
-- λx . f (x x)
ycombBody = Lambda 201 (Applic (Var 200) (Applic (Var 201) (Var 201)))
-- λf . (λx . f (x x)) (λx . f (x x))
ycomb = Lambda 200 (Applic ycombBody ycombBody)
-- λx . λy . (x, y)
toPair = Lambda 50 (Lambda 51 (Pair (Var 50) (Var 51)))
-- λx . let a = isZero x in a
isNotZero = Lambda 50 (LetIn 51 (Applic isZero (Var 50)) (Var 51))

a = TRec 50 (TFunction (TVar 50) (TVar 50))
aArrowA = TFunction a a

main = do
--       print $ typesEqual a aArrowA
       putStr "Omega\t\t\t\t\t\thas type "
       print $ typeProgram omegacomb
       putStr "λx . f (x x)\t\t\t\thas type "
       print $ typeProgram ycombBody
       putStr "Y Combinator\t\t\t\thas type "
       print $ typeProgram ycomb
       putStr "λx . λy . (x, y)\t\t\thas type "
       print $ typeProgram toPair
       putStr "λx . let a = isZero x in a\thas type "
       print $ typeProgram isNotZero
--       print $ unifyN 1 eqs
--       putStrLn "..."
--       print $ unifyN 20 eqs
       where
         typeProgram = \p -> lookup 0 $ fromMaybe [] $ unify $ toEquationSystem p