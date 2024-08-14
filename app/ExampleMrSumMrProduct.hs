module ExampleMrSumMrProduct where

import Data.Map (Map, fromList, (!))
import Data.SBV
import Data.List
import Logics
import Translation
import ToSBV


--------------------------
-- AGENTS and VARIABLES --
--------------------------
mrSum :: Agent 
mrSum = Agent {identity = "Mr Sum", nonobs = [m,n,theProduct]  } 
mrProduct :: Agent 
mrProduct = Agent {identity = "Mr Product", nonobs = [m,n,theSum] } 
m :: Var
m = NVar (2,100) ("m")
n :: Var
n = NVar (2,100) ("n")
theSum :: Var
theSum = NVar sumDom ("theSum")
theProduct :: Var
theProduct = NVar prodDom ("theProduct")

sumDom = (4,100)  
prodDom = (4,2500)

-----------------------------------------------------
-- Constraint Phi
-----------------------------------------------------
phi :: ModalFormula
phi = Conj [
            Atom (IVal n ≤ IVal m)
            ,Atom (IVal n ≤ I 63)
           ,Atom (IVal m ≤ I 63)
           ,Atom (I 2 ≤ IVal n)
           -- ,Atom (Eq (IVal theProduct) (I 35))-- debugging
           -- ,Atom (I 2 ≤ IVal theProduct)-- debugging
           ,Atom (IVal theSum ≤ I 136)
           -- ,Atom (IVal theProduct ≤ I 400)
           ,Atom (Eq  (IVal theSum) (Add (IVal m) (IVal n)))
           ,Atom (Eq  (IVal theProduct) (Mul (IVal m) (IVal n)))
           ]

-------------------------------------
-- Program C, Weakest Precondition --
-------------------------------------
annMrSum1 = Assert ((NegKVe mrSum theProduct) ∧ K mrSum (NegKVe mrProduct theSum)) 
annMrProduct = Assert (KVe mrProduct theSum) 
annMrSum2 = Assert (KVe mrSum theProduct) 

formulaNeg = (K mrSum (NegKVe mrProduct theSum))
-- formulaNeg = (Box annMrSum1 (NegKVe mrProduct theSum))
-- formulaNeg = (NegKVe mrProduct theSum) --debugging
formula = (KVe mrProduct theSum) --debugging
-- formula = (NegKVe mrProduct theSum) --debugging
-- formula = Neg ((NegKVe mrSum theProduct) ∧ K mrSum (NegKVe mrProduct theSum))
-- formula = Box (annMrSum1) (KVe mrSum theProduct) 
-- formula =  Box (Assert (K mrSum (Neg (KVe mrProduct theSum)))) (KVe mrProduct theSum)
mrSmrP = allSat $ toSBV [m, n, theSum, theProduct] phi (tau phi formula)   
mrSmrP_ = (tau phi formula)

uivarBound = maxUIBV (tau phi formula) 
xivarBound = maxEIBV (tau phi formula) 
writeSP  = writeFile "mrSmrP.py" (show uivarBound ++ "\n" ++ show xivarBound ++ "\n" ++ toPyString phi ++ "\n" ++ toPyString (tau phi formula))

mrSmrP2_prove_z =  proveWith z3 (toSBV [m, n, theSum, theProduct] (phi) (tau phi formulaNeg)) 
mrSmrP2_sat_z =  satWith z3 (toSBV [m, n, theSum, theProduct] (phi) (tau phi formula)) 
mrSmrP2_prove_c =  proveWith cvc4 (toSBV [m, n, theSum, theProduct] (phi) (tau phi formulaNeg)) 
mrSmrP2_sat_c =  satWith cvc4 (toSBV [m, n, theSum, theProduct] (phi) (tau phi formula)) 
mrSmrP2_prove_c5 =  proveWith cvc5 (toSBV [m, n, theSum, theProduct] (phi) (tau phi formulaNeg)) 
mrSmrP2_sat_c5 =  satWith cvc5 (toSBV [m, n, theSum, theProduct] (phi) (tau phi formula)) 
mrSmrP2_ =  (phi ∧ (tau phi formula)) 
