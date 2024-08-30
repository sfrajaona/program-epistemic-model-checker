module ExamplePit where

import Data.Map (Map, fromList, (!))
import Data.SBV
import Data.List
import Logics
import Translation
import ToSBV


--------------------------
-- AGENTS and VARIABLES --
--------------------------
a :: Agent 
a = Agent "a"
b :: Agent 
b = Agent "b"
c :: Agent 
c = Agent "c"

agents = [a,b,c] 

cardDom = (2,5)  -- the bounds of the domain

-- IMPORTANT NOTE --
-- In the theory a variable is indexed by the observing agents
-- here, in the implementation a variable is indexed by the non-ovserving agents

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
-- we define the functions pitSat and pitProve 

-- | pitProve takes a program epistemic formula alpha,
-- and tries to prove it in the context phi
-- i.e., it proves whether [[phi]] ⊧_LDK alpha
-- which correspond to [[phi]] ⊧_FO \tau (phi, alpha) by our main theorem
pitProve α = prove $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)
pitSat α = sat $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)
pitAllSat α = allSat $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)

------------ USAGE in GHCI ---------------
-- Make sure you have installed SBV.
-- First load the file
-- :l ExamplePit
--------------------------------

------------- Simple Test ---------------------
-- A can know that (la = 5)
-- >>> pitProve $ Neg (K a (Atom $ Eq (IVal la) (I 5)))
--  Falsifiable. Counter-example
--  la = 5 :: Integer
--  ra = 3 :: Integer
--  lb = 5 :: Integer
--  rb = 2 :: Integer
--  lc = 3 :: Integer
--  rc = 2 :: Integer
---------------------------------
  
---------------------------------
-- ACTIONs --  
-- swap1 = la <-> lb, using new hidden variables
-- players place their cards FACE DOWN on the table
---------------------------------

-- the cards on the table are represented by variables n and m
n = NVar [a,b,c] cardDom "n"
m = NVar [a,b,c] cardDom "m"

swap1 :: Prog
swap1 = New n (New m (Sequence [NAssign n (IVal la), NAssign m (IVal lb), NAssign lb (IVal n), NAssign la (IVal m)])) 


has :: Agent -> Integer -> ModalFormula
has ag i = ((Atom $ IVal (left ag) ≡ I i) ∨ (Atom $ IVal (right ag) ≡ I i)) 

alpha12 = Box swap1 (K b (Atom $ IVal lb ≡ IVal rb))
-- ^ B can know that lb=rb after swap1
-- ghci> pitProve $ Neg alpha12        or      ghci> pitSat alpha12
-- Falsifiable. Counter-example:
-- la = 3 :: Integer
-- ra = 2 :: Integer
-- lb = 5 :: Integer
-- rb = 3 :: Integer
-- lc = 5 :: Integer
-- rc = 2 :: Integer
alpha13 =Box swap1 ((Atom $ IVal lb ≡ IVal rb) ⇒ (Neg $ K a (Atom $ IVal lb ≡ IVal rb))) 
-- ^ A can never know that B makes a corner (lb=rb) after swap1
-- ghci> pitProve $ alpha13
-- Q.E.D
alpha14 = Box swap1 (Neg $ K a (Neg. Atom $ IVal lb ≡ IVal rb)) 
-- ^ A can learn that B does not make a corner (lb≠rb) after swap1
-- ghci> pitProve $ alpha14      or     ghci> pitSat $ Box swap1 (K a (Neg. Atom $ IVal lb ≡ IVal rb))
-- Falsifiable. Counter-example:
--  la = 3 :: Integer
--  ra = 2 :: Integer
--  lb = 3 :: Integer
--  rb = 5 :: Integer
--  lc = 2 :: Integer
--  rc = 5 :: Integer


alpha15 = Box swap1 (kv a lb) 
-- ^ A always knows the value of lb after swap1
-- ghci> pitProve alpha15 
-- Q.E.D

alpha16 = Box swap1 (K a (has c 5))
-- ^ A can learn that C has a 5 after swap1
-- ghci> pitProve $ Neg alpha16
-- Falsifiable. Counter-example:
-- la = 5 :: Integer
-- ra = 3 :: Integer
-- lb = 3 :: Integer
-- rb = 2 :: Integer
-- lc = 5 :: Integer
-- rc = 2 :: Integer
--
-- (a knows that c must have a 5 otherswise c must have two 2s, which is impossible)


---------------------------------
-- ACTIONs --  Nondeterministic swap 
-- swap2 = (la <-> lb) ⊔ (la <-> rb) ⊔ (ra <-> lb) ⊔ (ra <-> rb)
-- players place their cards *** FACE DOWN *** on the table
---------------------------------

swap :: Var -> Var -> Prog
swap u v = New n (New m (Sequence [NAssign n (IVal u), NAssign m (IVal v), NAssign v (IVal n), NAssign u (IVal m)]))

swap2 :: Prog
swap2 = swap la lb ⊔ swap la rb ⊔ swap ra lb ⊔ swap ra rb

alpha21 = Box swap2 (kv a lb) 
-- ^ A does not always know the value of lb after swap2
-- ghci> pitProve alpha21
-- Falsifiable. Counter-example:
--  la = 5 :: Integer
--  ra = 2 :: Integer
--  lb = 5 :: Integer
--  rb = 3 :: Integer
--  lc = 3 :: Integer
--  rc = 2 :: Integer

alpha22 = Box swap2 ((kv a lb) ∨ (kv a rb))
-- ^ A always knows the either value of lb or the value of rb after swap2
-- ghci> pitProve alpha22
-- Q.E.D
--
alpha23 = Box swap2 ( Neg (kv c lb))
-- ^ C never learns lb or rb after swap2
-- ghci> pitProve $ alpha23
-- Q.E.D


---------------------------------
-- ACTIONs --  Nondeterministic swap 
-- swap3 = (la <-> lb) ⊔ (la <-> rb) ⊔ (ra <-> lb) ⊔ (ra <-> rb)
-- players place their cards *** FACE UP *** on the table
-- now this action affect the knowledge of C unlike the previous swaps
---------------------------------

-- the cards on the table (visible for all this time)  are represented by variables 
-- n' and m'
n' = NVar [] cardDom "n"
m' = NVar [] cardDom "m"

swap' :: Var -> Var -> Prog
swap' u v = New n' (New m' (Sequence [NAssign n' (IVal u), NAssign m' (IVal v), NAssign v (IVal n'), NAssign u (IVal m')]))

swap3 :: Prog
swap3 = swap' la lb ⊔ swap' la rb ⊔ swap' ra lb ⊔ swap' ra rb

alpha31 = Box swap3 ((kv c lb) ∨ (kv c rb))
-- ^ C either learns lb or rb after swap3
-- ghci> pitProve $ alpha33
-- Q.E.D

alpha32 = Box swap3 ((kv c lb) ∧ (kv c rb))
-- ^ C does not always learns both lb or rc after swap3
-- ghci> pitProve $ alpha32
-- Falsifiable. Counter-example:
--  la = 3 :: Integer
--  ra = 5 :: Integer
--  lb = 5 :: Integer
--  rb = 2 :: Integer
--  lc = 3 :: Integer
--  rc = 2 :: Integer
--
--  e.g., with la <-> lb
--
-- ^ Actually, C can never always learn both lb or rc after swap3
-- ghci> pitProve $ Neg alpha32
-- Q.E.D

alpha33 = Box swap3 (Neg $ (K c (Atom $ IVal lb ≡ IVal rb)))
-- ^ C can know that B has corner after swap3
-- ghci> pitProve $  alpha33
-- Falsifiable. Counter-example:
--  la = 2 :: Integer
--  ra = 3 :: Integer
--  lb = 5 :: Integer
--  rb = 2 :: Integer
--  lc = 3 :: Integer
--  rc = 5 :: Integer

alpha34 = (Box swap3  (Neg $ K c (Neg . Atom $ IVal lb ≡ IVal rb)))
-- ^ C can know that B does not have a corner after swap3
-- ghci> pitProve $ alpha34
-- Falsifiable. Counter-example:
--  la = 5 :: Integer
--  ra = 2 :: Integer
--  lb = 3 :: Integer
--  rb = 2 :: Integer
--  lc = 3 :: Integer
--  rc = 5 :: Integer
-- 
-- e.g. with ra <-> rb, C sees that the exchange cards have the same suit
