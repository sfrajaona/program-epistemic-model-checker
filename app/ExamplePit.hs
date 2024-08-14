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
-- TODO IMPORTANT: variable are 
a :: Agent 
a = Agent "a"
b :: Agent 
b = Agent "b"
c :: Agent 
c = Agent "c"

cardDom = (2,5)  -- the bounds of the domain

la :: Var
la = NVar [b,c] cardDom ("la")
ra :: Var
ra = NVar [b,c] cardDom ("ra")

lb :: Var
lb = NVar [a,c] cardDom ("lb")
rb :: Var
rb = NVar [a,c] cardDom ("rb")

lc :: Var
lc = NVar [a,b] cardDom ("lc")
rc :: Var
rc = NVar [a,b] cardDom ("rc")



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
pitProve α = prove $ toSBV [la,ra,lb,rb,lc,rc] phi (tau phi α)

------------ USAGE in GHCI ---------------
-- Make sure you have installed SBV.
-- First load the file
-- :l ExamplePit
--------------------------------

---------------------------------
-- >>> pitSat $ KV a rb
-- Unsatisfiable
--
----------------------------------
-- >>> pitProve $ KV a ra
-- Q.E.D
--
----------------------------------
-- >>> pitSat $ KV a ra
--  Satisfiable. Model:
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
-- not a real swap DEBUGGING
-- swap1 = NAssign la (I 2) 
-- wp11 = wp (Atom (IVal la ≡ IVal ra)) swap1
-- wp12 = wp (K b $ Atom (IVal la ≡ IVal ra)) swap1


-- alpha11 = Box swap1 (Atom (IVal la ≡ IVal ra)) 
-- alpha12 = Box swap1 (K b (Atom (IVal la ≡ IVal ra)))
-- alpha13 = Box swap1 (K a (Atom (IVal la ≡ IVal ra)))

-- the real swap
n = NVar [a,b,c] cardDom "n"
swap2 = Sequence [New n (NAssign n (IVal la)), NAssign lb (IVal n)]
wp2 = wp (Atom (IVal la ≡ IVal ra)) swap2

alpha21 = Box swap2 (Atom (IVal lb ≡ IVal rb)) 
alpha22 = Box swap2 (K a (Atom (IVal lb ≡ IVal rb))) 
alpha23 = Box swap2 (K b (Atom (IVal lb ≡ IVal rb))) 

alpha24 = Box swap2 (KV a lb) 



