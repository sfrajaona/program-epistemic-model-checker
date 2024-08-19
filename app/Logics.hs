{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns  -fbang-patterns#-}
{-|
Module      : Logics

The module define the logical languages and everything that is needed inside them

* agents and variables 
* expressions (boolean and integer expressions),
* \(\mathcal{L_{DK}}, \mathcal{L_{\square K}}, \mathcal{L}_{FO}\) formulas
* programs inside the box
* weakest preconditions, strongest postconditions
* substitutions in expressions and formulas

See also the companion paper here https://doi.org/10.48550/arXiv.2206.13841
Maintainer: S.F. Rajaona sfrajaona@gmail.com
-}

module Logics where
import Data.SBV
import qualified Data.List as L
import Data.Int
import Data.Map (Map, fromList, (!))
import Debug.Trace

-- ==================
-- * Logic Syntax
-- ==================
----------------------------
-- ** Agents and Variables
--------------------------
data Agent = Agent String
   deriving (Eq, Ord)

instance Show Agent
  where
    show (Agent a) = a

-- | variables are string, we give a domain for integer variables
-- the domain is necessarily only if using SBV for 
-- variables are also labelled with a set of agents that cannot observe them
data Var = BVar [Agent] String | NVar [Agent] IntDomain String
   deriving (Eq, Ord)

type IntType = Integer
type IntDomain = (IntType,IntType)

-- | Function 'varName' returns the name of a variable (string) 
varName :: Var -> String
varName (BVar ags a) = a
varName (NVar ags d a) = a

varDom :: Var -> IntDomain
varDom (BVar ags a) = (0,1) 
varDom (NVar ags d a) = d

nonObservers :: Var -> [Agent] 
nonObservers (BVar ags _) = ags 
nonObservers (NVar ags _ _) = ags 

nonObs :: Agent -> ModalFormula -> [Var] 
nonObs a phi =  (L.nub [v | v <- freeVars phi, a `elem` nonObservers v]) 

------------------------------------------------
-- ** Expressions 
-- ------------------------------------------------
data Expr a where
    B       :: Bool -> Expr Bool        -- ^  Boolean constant 
    BSymb   :: SBool -> Expr Bool       -- ^  Boolean constant 
    BVal    :: Var -> Expr Bool         -- ^  Boolean variable
    BEq     :: Expr Bool -> Expr Bool -> Expr Bool
    Xoor    :: [Expr Bool] -> Expr Bool  
    Oor     :: [Expr Bool] -> Expr Bool
    Aand    :: [Expr Bool] -> Expr Bool
    I      :: IntType  -> Expr Integer     
    ISymb  :: SInteger  -> Expr Integer     
    IVal :: Var -> Expr Integer           
    Add    :: Expr Integer -> Expr Integer -> Expr Integer
    Mul    :: Expr Integer -> Expr Integer -> Expr Integer
    Eq     :: Expr Integer -> Expr Integer -> Expr Bool
    LEq    :: Expr Integer -> Expr Integer -> Expr Bool

type BExpr = Expr Bool
type NExpr = Expr Integer

-----------------------------------
-- ** Logic Formulas 
-- \(\mathcal{L_{DK}}, \mathcal{L_{\square K}}, \mathcal{L}_{FO} \) 
-----------------------------------
data Formula t where
   Atom      :: BExpr -> Formula t
   Neg       :: Formula t -> Formula t
   Conj      :: [Formula t] -> Formula t
   Disj      :: [Formula t] -> Formula t
   Imp       :: Formula t -> Formula t -> Formula t
   Equiv     :: Formula t -> Formula t -> Formula t
   K         :: Agent -> Formula Modal -> Formula Modal
   KV        :: Agent -> Var -> Formula Modal
   KVe       :: Agent -> Var -> Formula Modal
   NegKVe    :: Agent -> Var -> Formula Modal
   Ann       :: Formula Modal -> Formula Modal -> Formula Modal
   Box       :: Prog -> Formula Modal -> Formula Modal
   Box'      :: Prog -> Formula Modal -> Formula Modal
   ForAllB   :: Int -> [Agent] -> Formula Modal -> Formula Modal 
   ExistsB   :: Int -> [Agent] -> Formula Modal -> Formula Modal 
   ForAllI   :: Int -> [Agent] -> IntDomain -> Formula Modal -> Formula Modal 
   ExistsI   :: Int -> [Agent] -> IntDomain -> Formula Modal -> Formula Modal 

-- | Knowing whether modality
kw :: Agent -> ModalFormula -> ModalFormula
kw ag alpha = Disj [K ag alpha, (K ag (Neg alpha))]

data Modal
type ModalFormula = Formula Modal
    

-- ** Unicode shorthands
(∨) f g = Disj [f,g]  
(∧) f g = Conj [f,g]  
(⇒) f g = Imp f g
(⇔) f g = (f ∧ g) ∨ (Neg g ∧ Neg f)
true = Atom (B True)
false = Atom (B False)
(⊔) p q = Nondet [p, q]  
(≡) m n = Eq m n
(⨟) p q = Sequence [p, q]
(≤) m n = LEq m n
(⨰) m n = Mul m n 
(∔) m n = Add m n
(⊕) f g = Xoor [f, g] 

----------------------------------------------------------------------------
-- * Quantifiers Construction
----------------------------------------------------------------------------

-- | 'eBVar' constructs an existential boolean variable \(xb_i\) for an integer i 
eBVar :: Int -> [Agent] -> Var
eBVar n ags = BVar ags  ("XB[" ++ show n ++"]")

-- | 'uBVar' constructs an universal boolean variable \(ub_i\) for an integer i 
uBVar :: Int -> [Agent] -> Var
uBVar n ags = BVar ags ("UB[" ++ show n ++"]")

-- | 'eBVar' constructs an existential integer variable \(xi_i\) for an integer i 
eIVar :: Int -> [Agent] -> IntDomain -> Var
eIVar n ags d = NVar ags d ("XI[" ++ show n ++ "]")

-- | 'uBVar' constructs an universal integer variable \(ui_i\) for an integer i 
uIVar :: Int -> [Agent] -> IntDomain -> Var
uIVar n ags d = NVar ags d ("UI " ++ show n)

-- | this function chooses an appropriate index \(i\) 
-- to build universal quantification \(\exists y_i \ldots\)
-- from of a lambda abstracted 'ModalFormula'.
forAllB :: [Agent] -> (Var -> Formula Modal) -> Formula Modal
forAllB ags f = ForAllB n ags body
  where body = f (uBVar n ags)
        n    = (maxUBV body + 1)

-- | similar to 'forAllB' but with existential 
existsB :: [Agent] -> (Var -> Formula Modal) -> Formula Modal
existsB ags f = ExistsB n ags body
  where body = f (eBVar n ags)
        n    = maxEBV body + 1

-- | similar to 'forAllB' but for variables on other domains 
forAllI :: [Agent] -> IntDomain -> (Var ->  Formula Modal) -> Formula Modal
forAllI ags dom f = ForAllI n ags dom body
  where body = f (uIVar n ags dom)
        dummy = f (uIVar 0 ags dom)
        maxFvs = maximum [quantVarNum var | var <- freeVars dummy]
        n    = (maxUIBV body + 1) `max` maxFvs

quantVarNum :: Var -> Int
quantVarNum (NVar ags d str) | (head $ words str) == "UI" = read (last $ words str):: Int 
                             | otherwise = 0

-- | similar to 'existsB' but for non-bool domains
existsI :: [Agent] -> IntDomain -> (Var -> Formula Modal) -> Formula Modal
existsI ags dom f = ExistsI n ags dom body
  where body = f (eIVar n ags dom)
        n    = maxEIBV body + 1

-- Computes the maximum index of bound variables
maxEBV :: Formula Modal -> Int
maxEBV (Atom _  ) = 0
maxEBV (Neg f   ) = maxEBV f
maxEBV (Conj fs)  = maximum [maxEBV f | f <- fs]
maxEBV (Disj fs)  = maximum [maxEBV f | f <- fs]
maxEBV (Imp f g)  = maximum [maxEBV f, maxEBV g]
maxEBV (Equiv f g)  = maximum [maxEBV f, maxEBV g]
maxEBV (ExistsB n ags f) = n
maxEBV (ForAllB n ags f) = maxEBV f
maxEBV (ExistsI n ags d f) = maxEBV f
maxEBV (ForAllI n ags d f) = maxEBV f
maxEBV (K ag f) = maxEBV f 
maxEBV (KV ag v) = 0 
maxEBV (Ann f g) = maxEBV f `max` maxEBV g
maxEBV (Box p f) = maxEBV f 

maxUBV :: Formula Modal -> Int
maxUBV (Atom _  ) = 0
maxUBV (Neg f   ) = maxUBV f
maxUBV (Conj fs)  = maximum [maxUBV f | f <- fs]
maxUBV (Disj fs)  = maximum [maxUBV f | f <- fs]
maxUBV (Imp f g)  = maximum [maxUBV f, maxUBV g]
maxUBV (Equiv f g)  = maximum [maxUBV f, maxUBV g]
maxUBV (ExistsB n ags f) = maxUBV f
maxUBV (ForAllB n ags f) = n
maxUBV (ExistsI n ags d f) = maxUBV f
maxUBV (ForAllI n ags d f) = maxUBV f
maxUBV (K ag f) = maxUBV f 
maxUBV (KV ag v) = 0 
maxUBV (Ann f g) = maxUBV f `max` maxUBV g
maxUBV (Box p f) = maxUBV f 

-- Computes the maximum index of bound variables
maxEIBV :: Formula Modal -> Int
maxEIBV (Atom _  ) = 0
maxEIBV (Neg f   ) = maxEIBV f
maxEIBV (Conj fs)  = maximum [maxEIBV f | f <- fs]
maxEIBV (Disj fs)  = maximum [maxEIBV f | f <- fs]
maxEIBV (Imp f g)  = maximum [maxEIBV f, maxEIBV g]
maxEIBV (Equiv f g)  = maximum [maxEIBV f, maxEIBV g]
maxEIBV (ExistsB n ags f) = maxEIBV f
maxEIBV (ForAllB n ags f) = maxEIBV f
maxEIBV (ExistsI n ags d f) = n
maxEIBV (ForAllI n ags d f) = maxEIBV f
maxEIBV (K ag f) = maxEIBV f 
maxEIBV (KV ag v) = 0 
maxEIBV (Ann f g) = maxEIBV f `max` maxEIBV g
maxEIBV (Box p f) = maxEIBV f 

maxUIBV :: Formula Modal -> Int
maxUIBV (Atom _  ) = 0
maxUIBV (Neg f   ) = maxUIBV f
maxUIBV (Conj fs)  = maximum [maxUIBV f | f <- fs]
maxUIBV (Disj fs)  = maximum [maxUIBV f | f <- fs]
maxUIBV (Imp f g)  = maximum [maxUIBV f, maxUIBV g]
maxUIBV (Equiv f g)  = maximum [maxUIBV f, maxUIBV g]
maxUIBV (ExistsB n ags f) = maxUIBV f
maxUIBV (ForAllB n ags f) = maxUIBV f
maxUIBV (ExistsI n ags d f) = maxUIBV f
maxUIBV (ForAllI n ags d f) = n
maxUIBV (K ag f) = maxUIBV f 
maxUIBV (KV ag v) = 0 
maxUIBV (KVe ag v) = 0 
maxUIBV (Ann f g) = maxUIBV f `max` maxUIBV g
maxUIBV (Box p f) = maxUIBV f 

----------------------------
-- * Programming Language
----------------------------
-- ** Program Syntax
data Prog
    = Assume ModalFormula
    | Assert ModalFormula
    | BAssign Var BExpr 
    | NAssign Var NExpr 
    | New Var Prog 
    | Sequence [Prog]
    | Nondet [Prog]

----------------------------
-- ** Strongest Precondition Semantics
-- for comparing with IJCAI'17 paper
----------------------------
sp :: ModalFormula -> Prog -> ModalFormula
-- ^ Strongest postcondition semantics
-- TODO add sp for new
sp phi (Assume beta)       = beta ∧ phi
sp phi (Assert beta)       = beta ⇒ phi
sp phi (BAssign v e)     = existsB (nonObservers v) (\y -> Conj [Atom (BEq (BVal v) (subBExpr v (BVal y) e)), sub v (BVal y) phi])  
sp phi (NAssign v e)     = existsI (nonObservers v) (varDom v) (\y -> Conj [Atom (Eq (IVal v) (subNExpr v (IVal y) e)), sub v (IVal y) phi])  
sp phi (Sequence [])     = phi
sp phi (Sequence [p])    = sp phi p
sp phi (Sequence (p:ps)) = sp (sp phi p) (Sequence ps)
sp phi (Nondet ps)       = Disj [sp phi p | p <- ps]


----------------------------
-- ** Weakest preconditions Semantics
-- TODO: add wp for integer assignment
----------------------------
wp :: ModalFormula -> Prog -> ModalFormula
wp alpha (Assume beta)           = Ann beta alpha
wp alpha (Assert beta)           = beta ∧ Ann beta alpha
wp alpha (New (NVar ags d v) prog)   = forAllI ags d (\k -> (sub (NVar ags d v) (IVal k) (wp alpha prog)))
wp alpha (New (BVar ags v) prog)   = forAllB ags (\k -> (sub (BVar ags v) (BVal k) (wp alpha prog)))
wp alpha (BAssign v e)           = forAllB (nonObservers v) (\k -> (Ann (Atom (BEq (BVal k) e)) (sub v (BVal k) alpha)))
wp alpha (NAssign v e)           = forAllI (nonObservers v) (varDom v) (\k -> (Ann (Atom (Eq (IVal k) e)) (sub v (IVal k) alpha)))
wp alpha (Sequence [p])           = wp alpha p
wp alpha (Sequence (p:ps))       = wp (wp alpha (Sequence ps)) p
wp alpha (Nondet ps)             = Conj [wp alpha p | p <- ps]

-- ============
-- * Utility functions 
-- ============
--------------------------------
-- ** Substitution 
----------------------------
-- | sub is the main function, takes the variable, an expression, and the formula
-- to make the substitution
sub :: Var -> Expr a -> Formula b -> Formula b
sub x (I i) f      = subNum x (I i) f
sub x (ISymb i) f  = subNum x (ISymb i) f
sub x (IVal y) f = subNum x (IVal y) f
sub x (Add a b) f  = subNum x (Add a b) f
sub x (Mul a b) f  = subNum x (Mul a b) f
sub x (Eq a b) f   = subBool x (Eq a b) f
sub x (LEq a b) f  = subBool x (LEq a b) f
sub x (B b) f      = subBool x (B b) f
sub x (BSymb z) f  = subBool x (BSymb z) f
sub x (BVal p) f = subBool x (BVal p) f
sub x (Xoor bs) f   = subBool x (Xoor bs) f
sub x (Aand bs) f   = subBool x (Aand bs) f
sub x (Oor bs) f    = subBool x (Oor bs) f

-- | 'subNExpr'  propagates a substitution inside a numerical/integer expression
subNExpr :: Var -> NExpr -> NExpr -> NExpr
subNExpr x e (Add a b)               = Add (subNExpr x e a)  (subNExpr x e b)
subNExpr x e (Mul a b)               = Mul (subNExpr x e a)  (subNExpr x e b)
subNExpr x e (I i)                   = I i
subNExpr x e (ISymb i)               = ISymb i
subNExpr x e (IVal y) | x == y     = e
subNExpr x e (IVal y) | otherwise  = IVal y

-- | 'subBExpr' propagates a substitution inside a boolean expression
subBExpr :: Var -> BExpr -> BExpr -> BExpr
subBExpr x e (B b)                   = B b
subBExpr x e (BSymb b)                   = BSymb b
subBExpr x e (BVal z) | x == z     = e
subBExpr x e (BVal z) | otherwise  = BVal z
subBExpr x e (Xoor bs)                = Xoor [subBExpr x e b | b <- bs]
subBExpr x e (Aand bs)                = Aand [subBExpr x e b | b <- bs]
subBExpr x e (Oor bs)                 = Oor [subBExpr x e b | b <- bs]
subBExpr x e (Eq m n)                = Eq m n
subBExpr x e (LEq m n)               = LEq m n
subBExpr x e (BEq p q)               = BEq (subBExpr x e p) (subBExpr x e q)  

-- | 'subBool' propagates the substitution made inside a boolean expressions into a formula
subBool :: Var -> BExpr -> Formula a -> Formula a
subBool x e (Atom z)        = Atom (subBExpr x e z)
subBool x e (Neg f)         = Neg (subBool x e f)
subBool x e (Conj fs)       = Conj [subBool x e f | f <- fs]
subBool x e (Disj fs)       = Disj [subBool x e f | f <- fs]
subBool x e (Imp f g)       = Imp (subBool x e f) (subBool x e g)
subBool x e (Equiv f g)     = Equiv (subBool x e f) (subBool x e g)
subBool x e (K a f)         = K a (subBool x e f)
subBool x e (Ann f g)       = Ann (subBool x e f) (subBool x e g)
subBool x e (Box prog f)    = Box prog (subBool x e f)
subBool x e (ForAllB n ags f)     = ForAllB n ags (subBool x e f)  
subBool x e (ExistsB n ags f)     = ExistsB n ags (subBool x e f)  
subBool x e (ForAllI n ags d f)   = ForAllI n ags d (subBool x e f)  
subBool x e (ExistsI n ags d f)   = ExistsI n ags d (subBool x e f)  

-- | 'subNum' propagates the substitution inside integer expressions into a formula
subNum :: Var -> NExpr -> Formula a -> Formula a
subNum x e (Atom (Eq m n))   = Atom (Eq (subNExpr x e m)  (subNExpr x e n))
subNum x e (Atom (LEq m n))  = Atom (LEq (subNExpr x e m)  (subNExpr x e n))
subNum x e (Atom (BVal z)) = Atom (BVal z)
subNum x e (Atom (B b))      = Atom (B b)
subNum x e (Atom (Xoor bs))   = Atom (Xoor bs)
subNum x e (Atom (Aand bs))   = Atom (Aand bs)
subNum x e (Atom (Oor bs))    = Atom (Oor bs)
subNum x e (Neg f)           = Neg (subNum x e f)
subNum x e (Conj fs)         = Conj [subNum x e f | f <- fs]
subNum x e (Disj fs)         = Disj [subNum x e f | f <- fs]
subNum x e (Imp f g)         = Imp (subNum x e f) (subNum x e g)
subNum x e (Equiv f g)       = Equiv (subNum x e f) (subNum x e g)
subNum x e (K a f)           = K a (subNum x e f)
subNum x e (KV a v)          = KV a v
subNum x e (KVe a v)         = KVe a v
subNum x e (Ann f g)         = Ann (subNum x e f) (subNum x e g)
subNum x e (Box prog f)      = Box prog (subNum x e f)  -- no used
subNum x e (ForAllB n ags f)        = ForAllB n ags (subNum x e f)
subNum x e (ExistsB n ags f)        = ExistsB n ags (subNum x e f)
subNum x e (ForAllI n ags d f)      = ForAllI n ags d (subNum x e f)
subNum x e (ExistsI n ags d f)      = ExistsI n ags d (subNum x e f)

--------------------------------
-- ** Conversion to string
----------------------------

instance Show (Formula a) where
  show f = toString f

instance Show Var where
  -- TODO
  show (BVar ags a) = a++ show ags
  show (NVar ags d a) = a++show ags

instance Show (Expr a) where
  show (BVal v) = show v
  show (BEq p q) = show p ++ "==" ++ show q
  show (B True) = "T"
  show (B False) = "F"
  show (Xoor bs) = "allXoor([" ++ separateWithCommas [show b | b <- bs]  ++ "])"
  show (Oor [b]) = show b
  show (Oor (b:bs)) = show b ++ "∨" ++ show (Oor bs) 

  show (Aand [b]) = show b
  show (Aand (b:bs)) = show b ++ "∧" ++ show (Aand bs) 
  show (I a) = show a
  show (IVal a) = show a
  show (Eq m n) = show m ++ "==" ++ show n
  show (LEq m n) = show m ++ "<=" ++ show n
  show (Mul m n) = show m ++ "*" ++ show n
  show (Add m n) = show m ++ "+" ++ show n


instance Show Prog where
  show (Assume f) = (toString f) ++ "?"
  show (Assert f) = (toString f) ++ "!"
  show (BAssign v e) = show v ++ ":=" ++ show e
  show (NAssign v e) = show v ++ ":=" ++ show e
  show (Sequence []) = ""
  show (Sequence [p]) = show p
  show (Sequence (p:ps)) = show p ++ ";" ++ show (Sequence ps) 
  show (Nondet [] ) = ""
  show (Nondet [p] ) = show p
  show (Nondet (p:ps)) = show p ++ "⊓" ++ show (Sequence ps) 
-- precedence rules to decide parentheses
precedence :: Formula t -> Int
precedence Atom{} = 10 
precedence Neg {} = 9
precedence Conj{} = 8
precedence Disj{} = 7
precedence Imp{} = 6
precedence Equiv{} = 5
precedence K{} = 4 
precedence Ann{} = 3
precedence Box{} = 2 
precedence ForAllB{} = 1 
precedence ExistsB{} = 1 
precedence ForAllI{} = 1 
precedence ExistsI{} = 1 

-- | 'toString' takes any formula ('FOLFormula' or 'ModalFormula') 
-- and returns a pretty string. 
toString :: Formula a -> String
toString = toStringPrec 0


-- | 'toPythonString' is formatted to be parsable by Z3py and CVC5.pythonic.
toPyString :: Formula a -> String
toPyString = toPyStringPrec 0

toPyStringPrec :: Int -> Formula a -> String
toPyStringPrec dCntxt f = bracket unbracketed where
    dHere       = precedence f
    recurse     = toPyStringPrec dHere
    unbracketed = case f of
        Atom (B t)    -> show t
        Atom (BVal (BVar ags b))    -> b 
        Atom (Xoor (bs))  -> "allXoor([" ++ separateWithCommas [recurse (Atom b) | b <- bs]  ++ "])"
        Atom e -> show e
        K ag p   -> "K_" ++ (show ag) ++ " " ++ recurse p
        Ann f g   -> "[" ++ recurse f ++ "]" ++ recurse g
        Neg p   -> "Not(" ++ recurse p ++ ")"
        Conj [] -> "True"
        Disj [] -> "False" 
        Conj [p] -> recurse p
        Disj [p] -> recurse p 
        Conj (ps) -> "And([" ++ separateWithCommas [recurse p | p <- ps] ++ "])"
        Disj (ps) -> "Or([" ++ separateWithCommas [recurse p | p <- ps] ++ "])"
        Imp p q -> "Implies(" ++ recurse p ++ "," ++ recurse q ++ ")"
        Equiv p q -> "Equiv(" ++ recurse p ++ "," ++ recurse q ++ ")"
        Box prog q -> "{" ++ (show prog) ++ "}" ++ recurse q
        ExistsB b ags f -> "Exists(XB[" ++ show b ++ "], " ++ show ags ++ recurse f++ ")"
        ForAllB b ags f -> "ForAll(UB[" ++ show b ++ "], "++ show ags ++ recurse f++ ")"
        ExistsI b ags d f -> "Exists(XI[" ++ show b ++ "], "++ show ags ++ recurse f++ ")"
        ForAllI b ags d f -> "ForAll(UI[" ++ show b ++ "], "++ show ags ++ recurse f++ ")"
    bracket
        | dCntxt > dHere = \s -> "(" ++ s ++ ")"
        | otherwise      = id

toStringPrec :: Int -> Formula a -> String
toStringPrec dCntxt f = bracket unbracketed where
    dHere       = precedence f
    recurse     = toStringPrec dHere
    unbracketed = case f of
        Atom (B t)    -> show t
        Atom (BVal (BVar ags b))    -> b 
        Atom (Xoor (bs))  -> "allXoor([" ++ separateWithCommas [recurse (Atom b) | b <- bs]  ++ "])"
        Atom e -> show e
        K ag p   -> "K_" ++ (show ag) ++ " " ++ recurse p
        Ann f g   -> "[" ++ recurse f ++ "]" ++ recurse g
        Neg p   -> "¬" ++ recurse p
        Conj [] -> "True"
        Disj [] -> "False" 
        Conj [p] -> recurse p
        Disj [p] -> recurse p 
        Conj (p:ps) -> recurse p ++ " ∧ " ++ recurse (Conj ps) 
        Disj (p:ps) -> recurse p ++ " ∨ " ++ recurse (Disj ps) 
        Imp p q -> recurse p ++ " ⇒ " ++ recurse q
        Equiv p q -> recurse p ++ " ⇔ " ++ recurse q
        Box prog q -> "{" ++ (show prog) ++ "}" ++ recurse q
        ExistsB b ags f -> "∃yb" ++ show b ++ show ags  ++ "⋅"++ recurse f
        ForAllB b ags f -> "∀ub" ++ show b ++ show ags ++ "⋅"++ recurse f
        ExistsI b ags d f -> "∃XI[" ++ show b ++ "]"++ show ags ++"⋅" ++recurse f
        ForAllI b ags d f -> "∀UI[" ++ show b ++ "]"++ show ags ++"⋅" ++recurse f
    bracket
        | dCntxt > dHere = \s -> "(" ++ s ++ ")"
        | otherwise      = id


separateWithCommas :: [String] -> String
separateWithCommas [b] = b
separateWithCommas (b:bs) = b ++ ", " ++ separateWithCommas bs

-- ----------------------------
-- ** Free Variables
-- ----------------------------
class Varable a where
    freeVars0 :: a -> [Var]  
    freeVars  :: a -> [Var] 

instance Varable (Formula t)
    where
      freeVars f = (L.nub (freeVars0 f)) 
      freeVars0 (Atom b) = freeVars0 b
      freeVars0 (Neg f) = freeVars0 f
      freeVars0 (Conj fs) = concatMap freeVars0 fs
      freeVars0 (Disj fs) = concatMap freeVars0 fs
      freeVars0 (Imp f g) = freeVars0 f ++ freeVars0 g
      freeVars0 (Equiv f g) = freeVars0 f ++ freeVars0 g
      freeVars0 (K a f) = freeVars0 f
      freeVars0 (KV ag v) = [v] 
      freeVars0 (KVe ag v) = [v] 
      freeVars0 (NegKVe ag v) = [v] 
      freeVars0 (Ann f g) = freeVars0 f ++ freeVars0 g
      freeVars0 (Box f g) = freeVars0 f ++ freeVars0 g
      freeVars0 (Box' f g) = freeVars0 f ++ freeVars0 g
      freeVars0 (ForAllB i ags f) = freeVars0 f
      freeVars0 (ExistsB i ags f) = freeVars0 f
      freeVars0 (ForAllI i ags d f) = freeVars0 f
      freeVars0 (ExistsI i ags d f) = freeVars0 f

instance Varable (Expr a) 
  where
    freeVars f = L.nub (freeVars0 f)
    freeVars0 (B b) = []  
    freeVars0 (BSymb b) = []  
    freeVars0 (BVal v) = [v]  
    freeVars0 (BEq b b') = freeVars0 b ++ freeVars0 b'
    freeVars0 (Xoor bs) = concatMap freeVars0 bs
    freeVars0 (Oor bs) = concatMap freeVars0 bs
    freeVars0 (Aand bs) = concatMap freeVars0 bs
    freeVars0 (I n) = []  
    freeVars0 (ISymb n) = []  
    freeVars0 (IVal v) = [v]  
    freeVars0 (Add n n') = freeVars0 n ++ freeVars0 n'
    freeVars0 (Mul n n') = freeVars0 n ++ freeVars0 n'
    freeVars0 (Eq n n') = freeVars0 n ++ freeVars0 n'
    freeVars0 (LEq n n') = freeVars0 n ++ freeVars0 n'

instance Varable Prog 
  where
    freeVars p = L.nub (freeVars0 p)
    freeVars0 (New n p) = n:freeVars0 p 
    freeVars0 (Assume f) = freeVars0 f 
    freeVars0 (Assert f) = freeVars0 f 
    freeVars0 (BAssign v e) = v:freeVars0 e 
    freeVars0 (NAssign v e) = v:freeVars0 e 
    freeVars0 (Sequence ps) = concatMap freeVars0 ps
    freeVars0 (Nondet ps) = concatMap freeVars0 ps
