module ExamplePitExtra where

import Data.Map (Map, fromList, (!))
import Data.SBV
import Data.List
import Logics
import Translation
import ToSBV


--------------------------
-- AGENTS and VARIABLES --
--------------------------
-- TODO IMPORTANT: variable are 
a :: Agent 
a = Agent "a"
b :: Agent 
b = Agent "b"
c :: Agent 
c = Agent "c"

agents = [a,b,c] 

cardDom = (2,5)  -- the bounds of the domain

left :: Agent -> Var
left (Agent ag) = NVar (agents\\[Agent ag]) cardDom ("l"++ag) 

right :: Agent -> Var
right (Agent ag) = NVar (agents\\[Agent ag]) cardDom ("r"++ag) 

la = left a
ra = right a
lb = left b
rb = right b
lc = left c
rc = right c

-- la :: Var
-- la = NVar [b,c] cardDom ("la")
-- ra :: Var
-- ra = NVar [b,c] cardDom ("ra")

-- lb :: Var
-- lb = NVar [a,c] cardDom ("lb")
-- rb :: Var
-- rb = NVar [a,c] cardDom ("rb")

-- lc :: Var
-- lc = NVar [a,b] cardDom ("lc")
-- rc :: Var
-- rc = NVar [a,b] cardDom ("rc")



-----------------------------------------------------
-- Constraint Phi
-----------------------------------------------------

-- each of the players cards is represented by they prime numbers in {2,3,5} 
-- wheat = w is represented by the value 2
-- rye = y is represented by the value 3
-- flax = x is represented by the value 5
--
-- First constraint: each player's cards  ra,la,rb,lb,rc,lc is in {2,3,5} 
--
-- Second constraint: in the deck there are 2 wheat cards, 2 rye cards, and 2 flax cards 
-- the product of all players cards = 2x2x3x3x5x5 = 900
--
-- Third constraint: each player does not start with a pit, i.e., their first cards are of different suit

-- | we define a sequence of multiplications
--
mul :: [NExpr] -> NExpr 
mul [expr] = expr 
mul (l:ls) = Mul (l) (mul ls) 

phi :: ModalFormula
phi = Conj [
            Atom (Eq  (IVal ra) (I 2) ) ∨ Atom (Eq  (IVal ra) (I 3)) ∨ Atom (Eq  (IVal ra) (I 5))
           ,Atom (Eq  (IVal la) (I 2) ) ∨ Atom (Eq  (IVal la) (I 3)) ∨ Atom (Eq  (IVal la) (I 5))
           ,Atom (Eq  (IVal rb) (I 2) ) ∨ Atom (Eq  (IVal rb) (I 3)) ∨ Atom (Eq  (IVal rb) (I 5))
           ,Atom (Eq  (IVal lb) (I 2) ) ∨ Atom (Eq  (IVal lb) (I 3)) ∨ Atom (Eq  (IVal lb) (I 5))
           ,Atom (Eq  (IVal rc) (I 2) ) ∨ Atom (Eq  (IVal rc) (I 3)) ∨ Atom (Eq  (IVal rc) (I 5))
           ,Atom (Eq  (IVal lc) (I 2) ) ∨ Atom (Eq  (IVal lc) (I 3)) ∨ Atom (Eq  (IVal lc) (I 5))
           ,Atom (Eq (mul [IVal ra, IVal la, IVal rb, IVal lb, IVal rc, IVal lc]) (I 900))
           ,Neg (Atom (Eq  (IVal lc) (IVal rc) ))
           ,Neg (Atom (Eq  (IVal lb) (IVal rb) ))
           ,Neg (Atom (Eq  (IVal la) (IVal ra) ))
           ]

--------------------------------
-- Simple TESTS 
--------------------------------
-- we define the functions pitSat and pitProve to performs simple tests
--
pitSat α = sat $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)
pitAllSat α = allSat $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)
pitProve α = prove $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)

------------ USAGE in GHCI ---------------
-- Make sure you have installed SBV.
-- First load the file
-- :l ExamplePit
--------------------------------

----------------------------------
-- >>> pitProve $ KV a ra
-- Q.E.D
--
----------------------------------
-- >>> pitProve $ Neg (KV a ra)
--  Falsifiable. Counter-example
--  la = 5 :: Integer
--  ra = 3 :: Integer
--  lb = 5 :: Integer
--  rb = 2 :: Integer
--  lc = 3 :: Integer
--  rc = 2 :: Integer
---------------------------------
  
---------------------------------
-- ACTIONs
---------------------------------


-- the following action swap1 swaps la <-> lb
swap1 = New n (New m (Sequence [NAssign n (IVal la), NAssign m (IVal lb), NAssign lb (IVal n), NAssign la (IVal m)])) 

n = NVar [] cardDom "n"
m = NVar [] cardDom "m"

alpha21 = Neg $ Box swap1 (Atom $ IVal lb ≡ IVal rb) 
-- ^ Can  lb=rb after the swap? YES
-- ghci> pitProve alpha21
-- Falsifiable. Counter-example:
--  la = 3 :: Integer
--  ra = 2 :: Integer
--  lb = 5 :: Integer
--  rb = 3 :: Integer
--  lc = 2 :: Integer
--  rc = 5 :: Integer

alpha22 = Box swap1 ( K a (Atom $ IVal lb ≡ IVal rb)) 
-- ^ a can never learn that lb=rb after swap1
-- ghci> pitProve $ Neg alpha22
-- Q.E.D

has :: Agent -> Integer -> ModalFormula
has ag i = ((Atom $ IVal (left ag) ≡ I i) ∨ (Atom $ IVal (right ag) ≡ I i)) 

alpha32 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap1)  (K a (Atom $ IVal lb ≡ IVal rb))

swap2 = (Sequence [NAssign n (IVal la), NAssign m (IVal lb), NAssign lb (IVal n), NAssign la (IVal m)]) -- swap without new
swap4 = (NAssign n (IVal la)⨟ NAssign m (IVal lb)⨟ NAssign lb (IVal n)⨟ NAssign la (IVal m)) -- swap without new fatsemi
swap3 = (Sequence [NAssign n (IVal la), NAssign m (IVal ra), NAssign ra (IVal n), NAssign la (IVal m)]) -- swap ra and la

alpha33 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap1)  (K a (has c 3)) -- NOT OK

alpha34 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)))  (K a (has c 3)) -- OK

alpha35 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap2)  (K a (has c 3)) -- NOT OK

alpha39 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap2)  (K a (has c 3)) -- NOT OK

alpha36 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ NAssign la (I 5) ⨟ NAssign lb (I 3))  (K a (has c 3)) -- OK

alpha36' = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ NAssign la (IVal lb) ⨟ NAssign lb (I 3))  (K a (has c 3)) -- OK

alpha39' = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap4)  (K a (has c 3)) -- OK

alpha37 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap3)  (K a (has c 3)) -- OK

alpha38 = Box ((Assert $ (Atom $ IVal la ≡ I 3) ∧ (Atom $ IVal ra ≡ I 2) ∧ (Atom $ IVal lb ≡ I 5)) ⨟ swap1)  (phi) -- NOT OK

alpha0 = Box (NAssign la (IVal lb)) (kv a lb)  



alpha24 = Box swap1 (K a (Neg. Atom $ IVal lb ≡ IVal rb)) 
-- ^ Can a know that lb≠rb after the swap? YES
-- ghci> pitProve $ Neg alpha24
-- Falsifiable. Counter-example:
--  la = 3 :: Integer
--  ra = 2 :: Integer
--  lb = 3 :: Integer
--  rb = 5 :: Integer
--  lc = 2 :: Integer
--  rc = 5 :: Integer

alpha23 = Box swap1 (K b (Atom $ IVal lb ≡ IVal rb))
-- ^ Can b know that lb=rb after the swap? YES
-- ghci> pitProve $ Neg alpha23 
-- Falsifiable. Counter-example:
-- la = 3 :: Integer
-- ra = 2 :: Integer
-- lb = 5 :: Integer
-- rb = 3 :: Integer
-- lc = 5 :: Integer
-- rc = 2 :: Integer

kv :: Agent -> Var -> ModalFormula
kv a card = K a (Atom $ IVal card ≡ I 5) ∨ K a (Atom $ IVal card ≡ I 3) ∨ K a (Atom $ IVal card ≡ I 2)

alpha25 = Box swap1 (kv a lb) 
-- ^ Does a always know the value of lb after the swap? YES
-- ghci> pitProve alpha25 
-- Q.E.D


alpha27 = Box swap1 (K a (Neg (Atom $ IVal lb ≡ IVal rb))) 
-- ^ Can a know that b does not make corner after the swap? YES
-- ghci> pitProve $ Neg alpha27
-- Falsifiable. Counter-example:
-- la = 3 :: Integer
-- ra = 2 :: Integer
-- lb = 3 :: Integer
-- rb = 5 :: Integer
-- lc = 2 :: Integer
-- rc = 5 :: Integer

alpha28 = Box swap1 (K a (has c 5))
-- ^ Can a ever know that c has a 5? YES
-- ghci> pitProve $ Neg alpha28
-- Falsifiable. Counter-example:
-- la = 5 :: Integer
-- ra = 3 :: Integer
-- lb = 3 :: Integer
-- rb = 2 :: Integer
-- lc = 5 :: Integer
-- rc = 2 :: Integer
--
-- (a knows that c must have a 5 otherswise c must have two 2s, which is impossible)

alpha29 = Box swap1 ((K a (Neg (Atom $ IVal rb ≡ I 3))))

alpha20 = Atom $ B True



