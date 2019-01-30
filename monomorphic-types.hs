------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------
--------------------------------------- Monomorphic Typing Algorithm ---------------------------------------
------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import qualified Data.Map as Map

-- Definition of a program
data Program = Const Int
             | Var Int
             | Lambda Int Type Program
             | Fix Program
             | Applic Program Program
             | LetIn Int Type Program Program
             | IfElse Program Program Program
             deriving Show

-- Definition of a type
data Type = TInt | TBool | TPair Type Type | TFunction Type Type

-- Type alias for a type environment: a map from variables (int codes, as in Var Int) to types
type TypeEnv = Map Int Type

true  = -2
false = -1

-- Calculate the type of a given program in a given type environment
ptype :: TypeEnv -> Program -> Type

