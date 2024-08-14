{-|
Module   : ExampleCherylsBirthday
Description : Translation of the Cheryl's Birthday puzzle into a
  first-order satisfiability problem
  See also the companion paper here https://doi.org/10.48550/arXiv.2206.13841
Maintainer: S.F. Rajaona sfrajaona@gmail.com
-}
module ExampleCherylsBirthday where
import Data.List
import Logics
import Translation
import ToSBV 
import Data.SBV

--------------------------
-- AGENTS and VARIABLES --
--------------------------
albert  = Agent "Albert" 
bernard = Agent "Bernard" 
month   = NVar [bernard] monthDom ("month")
day     = NVar [albert] dayDom ("day")


--------------------
-- Constraint Phi --
--------------------
phi :: ModalFormula
phi = Disj [Atom (IVal month ≡ I 5) ∧ Atom (IVal day ≡ I 15),
            Atom (IVal month ≡ I 5) ∧ Atom (IVal day ≡ I 16),
            Atom (IVal month ≡ I 5) ∧ Atom (IVal day ≡ I 19),
            Atom (IVal month ≡ I 6) ∧ Atom (IVal day ≡ I 17),
            Atom (IVal month ≡ I 6) ∧ Atom (IVal day ≡ I 18),
            Atom (IVal month ≡ I 7) ∧ Atom (IVal day ≡ I 14),
            Atom (IVal month ≡ I 7) ∧ Atom (IVal day ≡ I 16),
            Atom (IVal month ≡ I 8) ∧ Atom (IVal day ≡ I 14),
            Atom (IVal month ≡ I 8) ∧ Atom (IVal day ≡ I 15),
            Atom (IVal month ≡ I 8) ∧ Atom (IVal day ≡ I 17)]

------------------------------------------
-- Program C  and  Weakest Precondition --
------------------------------------------
-- `KV x` means knowing the variable `x`
-- annAlbert1: "Albert does not know the day" and "Albert knows that Bernard does not know the month" 
-- annBernard: "Bernard annouces he knows the month now" 
--              the announcement "Bernard  didn't know the month before Albert's announcement"
--              is taken separately. In fact "this extra announcement" does not add information.
-- annAlbert2: "Albert annouces he knows the day now" 
  
  
albert1  = Neg (KV albert day) ∧ K albert (Neg (KV bernard month))
bernard1 = KV bernard month 
formula  = Box (Assert albert1 ⨟ Assert bernard1) (KV albert day)

-- ===========================================================================
--           Method 1:   Outputting the translation to an external file  
-- ===========================================================================
-- | writing the formulas into a file parsable by Z3py, containing 4 lines
-- line 1 : number of universally quantified variables
-- line 2 : number of existentially quantified variables
-- line 3 : first-order context ϕ
-- line 4 : translation τ(ϕ,α) 
uivarBound = maxUIBV (tau phi formula) 
xivarBound = maxEIBV (tau phi formula) 
writeForm  = writeFile "cherylsBirthday.py" (show uivarBound ++ "\n" ++ show xivarBound ++ "\n" ++ toPyString phi ++ "\n" ++ toPyString (tau phi formula))

-- ===========================================================================
--           Method 2:   Direct solution in Haskell with SBV
-- ===========================================================================
-- the solution with SBV requires transforming quantifiers into bounded conjunctions
-- hence we define the domain of the variables
-- monthDom = [5,6,7,8,9,10]       --  could be 1 to 12, smaller domain for performance
monthDom = (1,12)       --  could be 1 to 12, smaller domain for performance
-- dayDom = [14,15,16,17,18,19,21] --  could be 1 to 31
dayDom = (1,31) --  could be 1 to 31


-- USAGE
-- original version of the full puzzle
-- ------------------------------
-- cherylsBirthday = allSat $ toSBV [month, day] phi (tau phi (Conj [Neg (KV bernard month), formulaWp])) 

-- full puzzle but we can omit the the announcement Albert didn't know before
-- -----------------------------
cherylsBirthday = prove $ toSBV [month, day] phi (tau phi (Neg formula))
cherylsBirthdaySat = sat $ toSBV [month, day] phi (tau phi formula)
---------------------------------
------------ USAGE in GHCI ---------------
-- Make sure you have installed SBV.
-- First load the file
-- :l ExampleCherylsBirthday
--------------------------------


---------------------------------
-- >>> cherylsBirthday
-- Falsifiable. Counter-example:
-- month =  7 :: Integer
-- day   = 16 :: Integer
----------------------------------
-- >>> cherylsBirthdaySat
-- Satisfiable. Model:
-- month =  7 :: Integer
-- day   = 16 :: Integer
---------------------------------


-- not the full puzzle: check if [day=19?] KV_bernard month 
-- USAGE in GHCI: >>> CherylsBirthday2 
-- Solution #1:
  -- month =  5 :: Integer
  -- day   = 19 :: Integer
-- This is the only solution.
-- ----------------------------
frml2 =  Box (Assert $ Atom (IVal day ≡ I 19)) (KV bernard month)
cherylsBirthday2 = allSat $ toSBV [month, day] phi (tau phi frml2)

-- not the full puzzle: check if [day=17?] KV_bernard month 
-- USAGE in GHCI: >>> CherylsBirthday3 
--  No solutions found             
--  (Because there are two possible months with day=17 and bernard cannot distinguish them) 
-- ----------------------------
frml3 =  Box (Assert $ Atom (IVal day ≡ I 17)) (KV bernard month)
cherylsBirthday3 = allSat $ toSBV [month, day] phi (tau phi frml3)
