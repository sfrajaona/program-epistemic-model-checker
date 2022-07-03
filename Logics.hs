{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns  -fbang-patterns#-}
{-|
Module      : Logics

The module define the logical languages and everything that is needed inside them
* agents and variables 
* expressions (boolean and integer expressions),
* \mathcal{L_{DK}}, \mathcal{L_{\square K}}, \mathcal{L}_{FO} formulas
* programs inside the box
* weakest preconditions, strongest postconditions
* substitutions in expressions and formulas

See also the companion paper here https://doi.org/10.48550/arXiv.2206.13841
Maintainer: S.F. Rajaona sfrajaona@gmail.com
-}

module Logics where
import Data.SBV
import Data.Int
import Data.Map (Map, fromList, (!))
import Debug.Trace

----------------------------
-- * Agents and Variables
--------------------------
-- | an 'Agent' is determined by its identity and the set of nonobservable variables
data Agent = Agent {identity :: String, nonobs :: [Var]}
   deriving (Eq, Ord)

-- | variables are string, we give a domain for integer variables
-- the domain is necessarily only if using SBV, in which quantifications
-- are transformed into conjunctions/disjunctions
data Var = BVar String | NVar IntDomain String
   deriving (Eq, Ord)

type IntType = Integer
type IntDomain = [IntType]

-- | Function 'varname' returns the name of a variable (string) 
varname :: Var -> String
varname (BVar a) = a
varname (NVar d a) = a


------------------------------------------------
-- * Expressions (boolean expressions)
------------------------------------------------
data Expr a where
    B      :: Bool -> Expr Bool        -- ^ Boolean constant 
    BVal :: Var -> Expr Bool         -- ^ Boolean variable
    BEq    :: Expr Bool -> Expr Bool -> Expr Bool
    Xor    :: [Expr Bool] -> Expr Bool  
    Or     :: [Expr Bool] -> Expr Bool
    And    :: [Expr Bool] -> Expr Bool

    I      :: IntType  -> Expr Integer     
    IVal :: Var -> Expr Integer           
    Add    :: Expr Integer -> Expr Integer -> Expr Integer
    Mul    :: Expr Integer -> Expr Integer -> Expr Integer
    Eq     :: Expr Integer -> Expr Integer -> Expr Bool
    LEq    :: Expr Integer -> Expr Integer -> Expr Bool

type BExpr = Expr Bool
type NExpr = Expr Integer

-----------------------------------
-- * Logical Formulas \(\mathcal{L_{DK}}, \mathcal{L_{\square K}}, \mathcal{L}_{FO} \) 
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
   ForAllB   :: Int -> Formula Modal -> Formula Modal 
   ExistsB   :: Int -> Formula Modal -> Formula Modal 
   ForAllI   :: Int -> IntDomain -> Formula Modal -> Formula Modal 
   ExistsI   :: Int -> IntDomain -> Formula Modal -> Formula Modal 

kw :: Agent -> ModalFormula -> ModalFormula
kw ag alpha = Disj [K ag alpha, (K ag (Neg alpha))]

data Modal
type ModalFormula = Formula Modal

-- | Shotcuts
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
(⊕) f g = Xor [f, g] 

----------------------------------------------------------------------------
-- * Mechanism for dealing with quanitifiers
----------------------------------------------------------------------------

-- | 'eBVar' constructs an existential boolean variable \(xb_i\) for an integer i 
eBVar :: Int -> Var
eBVar n = BVar ("XB[" ++ show n ++"]")

-- | 'uBVar' constructs an universal boolean variable \(ub_i\) for an integer i 
uBVar :: Int -> Var
uBVar n = BVar ("UB[" ++ show n ++"]")

-- | 'eBVar' constructs an existential integer variable \(xi_i\) for an integer i 
eIVar :: Int -> IntDomain -> Var
eIVar n d = NVar d ("XI[" ++ show n ++ "]")

-- | 'uBVar' constructs an universal integer variable \(ui_i\) for an integer i 
uIVar :: Int -> IntDomain -> Var
uIVar n d = NVar d ("UI[" ++ show n ++ "]")

-- | this function chooses an appropriate index \(i\) 
-- to build universal quantification \(\exists y_i \ldots\)
-- from of a lambda abstracted 'ModalFormula'.
forAllB :: (Var -> Formula Modal) -> Formula Modal
forAllB f = ForAllB n body
  where body = f (uBVar n)
        n    = (maxUBV body + 1)

-- | similar to 'forAllB' but with existential 
existsB :: (Var -> Formula Modal) -> Formula Modal
existsB f = ExistsB n body
  where body = f (eBVar n)
        n    = maxEBV body + 1

-- | similar to 'forAllB' but for variables on other domains 
forAllI :: IntDomain -> (Var ->  Formula Modal) -> Formula Modal
forAllI dom f = ForAllI n dom body
  where body = f (uIVar n dom)
        n    = (maxUIBV body + 1)

-- | similar to 'existsB' but for non-bool domains
existsI :: IntDomain -> (Var -> Formula Modal) -> Formula Modal
existsI dom f = ExistsI n dom body
  where body = f (eIVar n dom)
        n    = maxEIBV body + 1

-- Computes the maximum index of bound variables
maxEBV :: Formula Modal -> Int
maxEBV (Atom _  ) = 0
maxEBV (Neg f   ) = maxEBV f
maxEBV (Conj fs)  = maximum [maxEBV f | f <- fs]
maxEBV (Disj fs)  = maximum [maxEBV f | f <- fs]
maxEBV (Imp f g)  = maximum [maxEBV f, maxEBV g]
maxEBV (Equiv f g)  = maximum [maxEBV f, maxEBV g]
maxEBV (ExistsB n f) = n
maxEBV (ForAllB n f) = maxEBV f
maxEBV (ExistsI n d f) = maxEBV f
maxEBV (ForAllI n d f) = maxEBV f
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
maxUBV (ExistsB n f) = maxUBV f
maxUBV (ForAllB n f) = n
maxUBV (ExistsI n d f) = maxUBV f
maxUBV (ForAllI n d f) = maxUBV f
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
maxEIBV (ExistsB n f) = maxEIBV f
maxEIBV (ForAllB n f) = maxEIBV f
maxEIBV (ExistsI n d f) = n
maxEIBV (ForAllI n d f) = maxEIBV f
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
maxUIBV (ExistsB n f) = maxUIBV f
maxUIBV (ForAllB n f) = maxUIBV f
maxUIBV (ExistsI n d f) = maxUIBV f
maxUIBV (ForAllI n d f) = n
maxUIBV (K ag f) = maxUIBV f 
maxUIBV (KV ag v) = 0 
maxUIBV (Ann f g) = maxUIBV f `max` maxUIBV g
maxUIBV (Box p f) = maxUIBV f 

----------------------------
-- * Programming Language
----------------------------
data Prog
    = Assume ModalFormula
    | Assert ModalFormula
    | BAssign Var BExpr 
    | Sequence [Prog]
    | Nondet [Prog]

----------------------------
-- * Strongest Precondition for comparing with IJCAI'17 paper
----------------------------
sp :: ModalFormula -> Prog -> ModalFormula
sp phi (Assume beta)       = beta ∧ phi
sp phi (Assert beta)       = beta ⇒ phi
sp phi (BAssign v e)     = existsB (\y -> Conj [Atom (BEq (BVal v) (subBExpr v (BVal y) e)), sub v (BVal y) phi])  
sp phi (Sequence [])     = phi
sp phi (Sequence [p])    = sp phi p
sp phi (Sequence (p:ps)) = sp (sp phi p) (Sequence ps)
sp phi (Nondet ps)       = Disj [sp phi p | p <- ps]


----------------------------
-- * Weakest preconditions
-- TODO: add wp for integer assignment
----------------------------
wp :: ModalFormula -> Prog -> ModalFormula
wp alpha (Assume beta)           = Ann beta alpha
wp alpha (Assert beta)           = beta ∧ Ann beta alpha
wp alpha (BAssign v e)           = forAllB (\k -> (Ann (Atom (BEq (BVal k) e)) (sub v (BVal k) alpha)))
wp alpha (Sequence [])           = alpha
wp alpha (Sequence (p:ps))       = wp (wp alpha (Sequence ps)) p
wp alpha (Nondet ps)             = Conj [wp alpha p | p <- ps]

--------------------------------
-- * Variable Substitution 
----------------------------
-- | sub is the main function, takes the variable, an expression, and the formula
-- to make the substitution
sub :: Var -> Expr a -> Formula b -> Formula b
sub x (I i) f      = subNum x (I i) f
sub x (IVal y) f = subNum x (IVal y) f
sub x (Add a b) f  = subNum x (Add a b) f
sub x (Mul a b) f  = subNum x (Mul a b) f
sub x (Eq a b) f   = subBool x (Eq a b) f
sub x (LEq a b) f  = subBool x (LEq a b) f
sub x (B b) f      = subBool x (B b) f
sub x (BVal p) f = subBool x (BVal p) f
sub x (Xor bs) f   = subBool x (Xor bs) f
sub x (And bs) f   = subBool x (And bs) f
sub x (Or bs) f    = subBool x (Or bs) f

-- | 'subNExpr'  propagates a substitution inside a numerical/integer expression
subNExpr :: Var -> NExpr -> NExpr -> NExpr
subNExpr x e (Add a b)               = Add (subNExpr x e a)  (subNExpr x e b)
subNExpr x e (Mul a b)               = Mul (subNExpr x e a)  (subNExpr x e b)
subNExpr x e (I i)                   = I i
subNExpr x e (IVal y) | x == y     = e
subNExpr x e (IVal y) | otherwise  = IVal y

-- | 'subBExpr' propagates a substitution inside a boolean expression
subBExpr :: Var -> BExpr -> BExpr -> BExpr
subBExpr x e (B b)                   = B b
subBExpr x e (BVal z) | x == z     = e
subBExpr x e (BVal z) | otherwise  = BVal z
subBExpr x e (Xor bs)                = Xor [subBExpr x e b | b <- bs]
subBExpr x e (And bs)                = And [subBExpr x e b | b <- bs]
subBExpr x e (Or bs)                 = Or [subBExpr x e b | b <- bs]
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
subBool x e (ForAllB n f)   = ForAllB n (subBool x e f)  
subBool x e (ExistsB n f)   = ExistsB n (subBool x e f)  
subBool x e (ForAllI n d f)   = ForAllI n d (subBool x e f)  
subBool x e (ExistsI n d f)   = ExistsI n d (subBool x e f)  

-- | 'subNum' propagates the substitution inside integer expressions into a formula
subNum :: Var -> NExpr -> Formula a -> Formula a
subNum x e (Atom (Eq m n))   = Atom (Eq (subNExpr x e m)  (subNExpr x e n))
subNum x e (Atom (LEq m n))  = Atom (LEq (subNExpr x e m)  (subNExpr x e n))
subNum x e (Atom (BVal z)) = Atom (BVal z)
subNum x e (Atom (B b))      = Atom (B b)
subNum x e (Atom (Xor bs))   = Atom (Xor bs)
subNum x e (Atom (And bs))   = Atom (And bs)
subNum x e (Atom (Or bs))    = Atom (Or bs)
subNum x e (Neg f)           = Neg (subNum x e f)
subNum x e (Conj fs)         = Conj [subNum x e f | f <- fs]
subNum x e (Disj fs)         = Disj [subNum x e f | f <- fs]
subNum x e (Imp f g)         = Imp (subNum x e f) (subNum x e g)
subNum x e (Equiv f g)       = Equiv (subNum x e f) (subNum x e g)
subNum x e (K a f)           = K a (subNum x e f)
subNum x e (Ann f g)         = Ann (subNum x e f) (subNum x e g)
subNum x e (Box prog f)      = Box prog (subNum x e f)  -- no used
subNum x e (ForAllB n f)        = ForAllB n (subNum x e f)
subNum x e (ExistsB n f)        = ExistsB n (subNum x e f)
subNum x e (ForAllI n d f)      = ForAllI n d (subNum x e f)
subNum x e (ExistsI n d f)      = ExistsI n d (subNum x e f)

--------------------------------
-- * Conversion to string
----------------------------

instance Show (Formula a) where
  show f = toString f

instance Show Var where
  show (BVar a) = a
  show (NVar d a) = a

instance Show (Expr a) where
  show (BVal v) = show v
  show (BEq p q) = show p ++ "==" ++ show q
  show (B True) = "T"
  show (B False) = "F"
  show (Xor bs) = "allXor([" ++ separateWithCommas [show b | b <- bs]  ++ "])"
  show (Or [b]) = show b
  show (Or (b:bs)) = show b ++ "∨" ++ show (Or bs) 
  show (And [b]) = show b
  show (And (b:bs)) = show b ++ "∧" ++ show (And bs) 
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
        Atom (BVal (BVar b))    -> b 
        Atom (Xor (bs))  -> "allXor([" ++ separateWithCommas [recurse (Atom b) | b <- bs]  ++ "])"
        Atom e -> show e
        K ag p   -> "K_" ++ (identity ag) ++ " " ++ recurse p
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
        ExistsB b f -> "Exists(XB[" ++ show b ++ "], "++ recurse f++ ")"
        ForAllB b f -> "ForAll(UB[" ++ show b ++ "], "++ recurse f++ ")"
        ExistsI b d f -> "Exists(XI[" ++ show b ++ "], "++ recurse f++ ")"
        ForAllI b d f -> "ForAll(UI[" ++ show b ++ "], "++ recurse f++ ")"
    bracket
        | dCntxt > dHere = \s -> "(" ++ s ++ ")"
        | otherwise      = id

toStringPrec :: Int -> Formula a -> String
toStringPrec dCntxt f = bracket unbracketed where
    dHere       = precedence f
    recurse     = toStringPrec dHere
    unbracketed = case f of
        Atom (B t)    -> show t
        Atom (BVal (BVar b))    -> b 
        Atom (Xor (bs))  -> "allXor([" ++ separateWithCommas [recurse (Atom b) | b <- bs]  ++ "])"
        Atom e -> show e
        K ag p   -> "K_" ++ (identity ag) ++ " " ++ recurse p
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
        ExistsB b f -> "∃yb" ++ show b ++ "⋅"++ recurse f
        ForAllB b f -> "∀ub" ++ show b ++ "⋅"++ recurse f
        ExistsI b d f -> "∃yi" ++ show b ++ "⋅"++ recurse f
        ForAllI b d f -> "∀ui" ++ show b ++ "⋅"++ recurse f
    bracket
        | dCntxt > dHere = \s -> "(" ++ s ++ ")"
        | otherwise      = id


separateWithCommas :: [String] -> String
separateWithCommas [b] = b
separateWithCommas (b:bs) = b ++ ", " ++ separateWithCommas bs
