import JMTypes

main = print $ unify eqs
         where 
            eqs = [(TVar 0, TVar 1), (TVar 2, TVar 3), (TVar 3, TInt), (TVar 4, TFunction (TInt) (TVar 1)), (TVar 1, TInt)]