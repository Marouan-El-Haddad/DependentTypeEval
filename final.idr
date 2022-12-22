import Data.Vect

-- TyExp represents the type of an expression
data TyExp
    = Tint
    | Tbool

-- Val is a type level function that takes a TyExp and returns a Type.
-- It maps Tint to Int and Tbool to Bool.
Val : TyExp -> Type
Val Tint = Int
Val Tbool = Bool

--I use a nameless representation for variables — they are de Bruijn indexed. 
--Variables are represented by a proof of their membership in the cntxt, 
--HasType i cntxt T, which is a proof that variable i in cntxt cntxt has type T. This is defined as follows:
data HasTypeVar : (i : Fin n) -> Vect n TyExp -> TyExp -> Type where
    StopVar : HasTypeVar FZ (tVar :: vcntxt) tVar 
    PopVar  : HasTypeVar kFin vcntxt tVar 
           -> HasTypeVar (FS kFin) (uVar :: vcntxt) tVar
--I can treat StopVar as a proof that the most recently defined variable is well-typed, 
--and PopVar n as a proof that, if the nth most recently defined variable is well-typed, 
--so is the n+1th. In practice, this means I use Stop to refer to the most recently defined variable, 
--PopVar StopVar to refer to the next, and so on, via the Var constructor
           
--This defines a new data type called Exp, which represents expressions in the language. 
--It takes three arguments: a vector of type expressions Vect n TyExp representing the type environment, 
--a pair of type expressions (TyExp, TyExp) representing the function environment, and a type expression TyExp representing the type of the expression.
data Exp : (vEnv: Vect n TyExp) -> (fEnv: (TyExp, TyExp)) -> TyExp -> Type where
  ExpVar : HasTypeVar iFin vEnv t -> Exp vEnv fEnv t
  ExpVal : (x : Int) -> Exp vEnv fEnv Tint
  ExpAddition : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpSubtraction : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpMultiplication : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint
  ExpIfThenElse : Exp vEnv fEnv Tbool -> Exp vEnv fEnv t -> Exp vEnv fEnv t -> Exp vEnv fEnv t
  ExpOr : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpAnd : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpNot : Exp vEnv fEnv Tbool -> Exp vEnv fEnv Tbool
  ExpEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpNotEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpLessThan : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpLessThanEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpGreaterThan : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpGreaterThanEqual : Exp vEnv fEnv Tint -> Exp vEnv fEnv Tint -> Exp vEnv fEnv Tbool
  ExpFuncCall: Exp vEnv (s,t) s -> Exp vEnv (s,t) t


record FunDecl where
  constructor MkFunDecl
  fd_var_type: TyExp
  fd_return_type: TyExp
  body: Exp [fd_var_type] (fd_var_type, fd_return_type) fd_return_type


record OpenProgram where
  constructor MkOpenProgram
  op_funDecl : FunDecl
  op_return_type: TyExp
  op_arg_type : TyExp
  val_arg : Val op_arg_type
  op_mainExp : Exp [op_arg_type] (op_funDecl.fd_var_type, op_funDecl.fd_return_type) op_return_type

record Program where
  constructor MkProgram
  p_funDecl: FunDecl
  p_return_type: TyExp
  p_mainExp: Exp [] (p_funDecl.fd_var_type, p_funDecl.fd_return_type) p_return_type

--This declares a data type called VarEnv that takes a value of the type Vect n TyExp and represents a variable environment:
data VarEnv : Vect n TyExp -> Type where
    Nil  : VarEnv Nil
    (::) : Val a 
            -> VarEnv ecntxt 
            -> VarEnv (a :: ecntxt)

--This is a function that takes a value of the type HasTypeVar i lcontex t and a value of the type VarEnv lcontex, and returns a value of the type Val t. The function looks up the value of the variable in the given environment using the HasTypeVar value.
lookupVar : HasTypeVar i lcontex t -> VarEnv lcontex -> Val t
lookupVar StopVar (x :: xs) = x
lookupVar (PopVar k) (x :: xs) = lookupVar k xs

evalOpenProg : (op: OpenProgram) -> Val op.op_return_type
evalOpenProg (MkOpenProgram op_funDecl op_return_type op_arg_type val_arg (ExpVar x)) = lookupVar x (val_arg :: Nil)
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpVal x)) = x
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpAddition x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) + evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpSubtraction x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) - evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tint op_arg_type val_arg (ExpMultiplication x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) * evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl op_return_type op_arg_type val_arg (ExpIfThenElse x y z)) = if evalOpenProg ( MkOpenProgram op_funDecl Tbool op_arg_type val_arg x) then evalOpenProg ( MkOpenProgram op_funDecl op_return_type op_arg_type val_arg y) else evalOpenProg (assert_smaller z $ MkOpenProgram op_funDecl op_return_type op_arg_type val_arg z)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpOr x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tbool op_arg_type val_arg x) || evalOpenProg ( MkOpenProgram op_funDecl Tbool op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpAnd x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tbool op_arg_type val_arg x) && evalOpenProg ( MkOpenProgram op_funDecl Tbool op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpNot x)) = not $ evalOpenProg ( MkOpenProgram op_funDecl Tbool op_arg_type val_arg x)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpEqual x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) == evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpNotEqual x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) /= evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpLessThan x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) < evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpLessThanEqual x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) <= evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpGreaterThan x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) > evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl Tbool op_arg_type val_arg (ExpGreaterThanEqual x y)) = evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg x) >= evalOpenProg ( MkOpenProgram op_funDecl Tint op_arg_type val_arg y)
evalOpenProg (MkOpenProgram op_funDecl (op_funDecl.fd_return_type) op_arg_type val_arg (ExpFuncCall x)) 
                = evalOpenProg (
                    MkOpenProgram op_funDecl (op_funDecl.fd_return_type) op_funDecl.fd_var_type (
                      evalOpenProg (
                        MkOpenProgram op_funDecl (op_funDecl.fd_var_type) op_arg_type val_arg x
                      ) 
                    ) op_funDecl.body
                ) 
              
evalProg : (p: Program) -> Val p.p_return_type
evalProg (MkProgram _ _ (ExpVar StopVar)) impossible
evalProg (MkProgram _ _ (ExpVar (PopVar x))) impossible
evalProg (MkProgram p_funDecl Tint (ExpVal x)) = x
evalProg (MkProgram p_funDecl Tint (ExpAddition x y)) = evalProg ( MkProgram p_funDecl Tint x) + evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tint (ExpSubtraction x y)) = evalProg ( MkProgram p_funDecl Tint x) - evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tint (ExpMultiplication x y)) = evalProg ( MkProgram p_funDecl Tint x) * evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl p_return_type (ExpIfThenElse x y z)) = if evalProg ( MkProgram p_funDecl Tbool x) then evalProg ( MkProgram p_funDecl p_return_type y) else evalProg (assert_smaller z $ MkProgram p_funDecl p_return_type z)
evalProg (MkProgram p_funDecl Tbool (ExpOr x y)) = evalProg ( MkProgram p_funDecl Tbool x) || evalProg ( MkProgram p_funDecl Tbool y)
evalProg (MkProgram p_funDecl Tbool (ExpAnd x y)) = evalProg ( MkProgram p_funDecl Tbool x) && evalProg ( MkProgram p_funDecl Tbool y)
evalProg (MkProgram p_funDecl Tbool (ExpNot x)) = not $ evalProg ( MkProgram p_funDecl Tbool x)
evalProg (MkProgram p_funDecl Tbool (ExpEqual x y)) = evalProg ( MkProgram p_funDecl Tint x) == evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpNotEqual x y)) = evalProg ( MkProgram p_funDecl Tint x) /= evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpLessThan x y)) = evalProg ( MkProgram p_funDecl Tint x) < evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpLessThanEqual x y)) = evalProg ( MkProgram p_funDecl Tint x) <= evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpGreaterThan x y)) = evalProg ( MkProgram p_funDecl Tint x) > evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl Tbool (ExpGreaterThanEqual x y)) = evalProg ( MkProgram p_funDecl Tint x) >= evalProg ( MkProgram p_funDecl Tint y)
evalProg (MkProgram p_funDecl (p_funDecl.fd_return_type) (ExpFuncCall x)) 
                = evalOpenProg (
                    MkOpenProgram p_funDecl (p_funDecl.fd_return_type) p_funDecl.fd_var_type (
                      evalProg (
                        MkProgram p_funDecl (p_funDecl.fd_var_type) x
                        )
                    ) p_funDecl.body 
                  )

----------------------------------------------------------------------------------------
--examples of using evalOpenProg and evalProg

-- Define a function that adds two integers
add : FunDecl
add = MkFunDecl Tint Tint (ExpAddition (ExpVal 1) (ExpVal 2))

-- Create an OpenProgram value that includes the add function and the necessary return type
prog1 : OpenProgram
prog1 = MkOpenProgram add Tint Tint 3 (ExpFuncCall (ExpVar (StopVar)))


-- Define a function that returns the square of an integer
square : FunDecl
square = MkFunDecl Tint Tint (ExpMultiplication (ExpVar (StopVar)) (ExpVar (StopVar)))

-- Create an OpenProgram value that includes the square function and the necessary return type
prog2 : OpenProgram
prog2 = MkOpenProgram square Tint Tint 3 (ExpMultiplication (ExpVal 2) (ExpVal 2))


-- Define a function that returns the square of an integer if the input is greater than 2, and the input itself otherwise
squareOrInput : FunDecl
squareOrInput = MkFunDecl Tint Tint (ExpIfThenElse (ExpGreaterThan (ExpVar (StopVar)) (ExpVal 2)) (ExpMultiplication (ExpVar (StopVar)) (ExpVar (StopVar))) (ExpVar (StopVar)))

-- Create an OpenProgram value that includes the squareOrInput function and the necessary return type
prog3 : OpenProgram
prog3 = MkOpenProgram squareOrInput Tint Tint 3 (ExpIfThenElse (ExpGreaterThan (ExpVal 2) (ExpVal 1)) (ExpMultiplication (ExpVal 2) (ExpVal 2)) (ExpVal 1))

-- Define a function that returns True if the input is greater than 10, and False otherwise
isGreaterThanTen : FunDecl
isGreaterThanTen = MkFunDecl Tint Tbool (ExpGreaterThan (ExpVar (StopVar)) (ExpVal 10))

-- Create an OpenProgram value that includes the isGreaterThanTen function and the necessary return type
prog4 : OpenProgram
prog4 = MkOpenProgram isGreaterThanTen Tbool Tint 12 (ExpGreaterThan (ExpVal 12) (ExpVal 10))


-- Define a function that returns True if the input is greater than 10, and False otherwise
isGreaterThanTen2 : FunDecl
isGreaterThanTen2 = MkFunDecl Tint Tbool (ExpGreaterThan (ExpVar (StopVar)) (ExpVal 10))

-- Create an OpenProgram value that includes the isGreaterThanTen function and the necessary return type
prog5 : OpenProgram
prog5 = MkOpenProgram isGreaterThanTen2 Tbool Tint 12 (ExpGreaterThan (ExpVal 12) (ExpVal 10))



-- Define a function that returns the nth fibonacci number
fib : FunDecl
fib = MkFunDecl Tint Tint (ExpIfThenElse (ExpLessThan (ExpVar (StopVar)) (ExpVal 2))
                                         (ExpVar (StopVar))
                                         (ExpAddition (ExpFuncCall (ExpSubtraction (ExpVar (StopVar)) (ExpVal 1)))
                                                      (ExpFuncCall (ExpSubtraction (ExpVar (StopVar)) (ExpVal 2)))))

-- Create an OpenProgram value that includes the fib function and the necessary return type
fibProg : OpenProgram
fibProg = MkOpenProgram fib Tint Tint 6 (ExpFuncCall (ExpVar (StopVar)))


-- Create a Program value that includes the fib function and the necessary return type
fibProg' : Program
fibProg' = MkProgram fib Tint (ExpFuncCall (ExpVal 6))

-- Define a function that returns the factorial of an integer
fact : FunDecl
fact = MkFunDecl Tint Tint (ExpIfThenElse (ExpLessThanEqual (ExpVar (StopVar)) (ExpVal 1))
                                          (ExpVal 1)
                                          (ExpMultiplication (ExpVar (StopVar)) (ExpFuncCall (ExpSubtraction (ExpVar (StopVar)) (ExpVal 1)))))

-- Create a Program value that includes the fact function and the necessary return type
factProg : Program
factProg = MkProgram fact Tint (ExpFuncCall (ExpVal 10))


--evalOpenProg prog1
--evalOpenProg prog2
--evalOpenProg prog3
--evalOpenProg prog4
--evalOpenProg prog5
--evalOpenProg fibProg
--evalProg fibProg'
--evalProg factProg
