module ExampleMrSumMrProduct where
import Data.Map (Map, fromList, (!))
import Data.SBV
import Data.List
import Logics
import ToSBV

--------------------------
-- AGENTS and VARIABLES --
--------------------------
mrSum = Agent {identity = "MrSum", nonobs = [m,n,theProd]  } 
mrProduct = Agent {identity = "MrProd", nonobs = [m,n,theSum] } 

m = NVar mDom ("M")
n = NVar nDom ("N")
theSum   = NVar sumDom ("S")
theProd  = NVar prodDom ("P")
vars = [m, n, theSum, theProd]

maxSum = 80 
maxProd = (maxSum `div` 2)*(maxSum `div` 2)

mDom    = [2 .. maxSum]
nDom    = [2 .. maxSum]
sumDom  = [2 .. maxSum]
prodDom = [2 .. maxProd]

-----------------------------------------------------
-- Constraint Phi
-----------------------------------------------------
phi = Conj  [ Atom (IVal n ≤ IVal m)
            , Atom (IVal m ≤ I maxSum)
            , Atom (I 2 ≤ IVal n)
            , Atom (IVal theSum ≡ (IVal m ∔ IVal n))
            , Atom (IVal theProd ≡ (IVal m ⨰ IVal n))
            ]

-------------------------------------
-- Formulas to be checked --
-------------------------------------
frml1  = K mrSum (Neg (KV mrProduct m))
frml2  = KV mrProduct m
frml3  = KV mrSum m
frml1e = NegKVe mrProduct m ∧ K mrSum (NegKVe mrProduct m)
frml2e  = KVe mrProduct m
frml3e  = KVe mrSum m
puzzl = Box (Assert frml1 ⨟ Assert frml2 ) frml3 -- original puzzle
puzzle = Box (Assert frml1e ⨟ Assert frml2e) frml3e -- original puzzle
puzzlTau = (tau phi puzzl)
puzzleTau = (tau phi frml1e)

uivarBound = maxUIBV puzzleTau 
xivarBound = maxEIBV puzzleTau 


writeForm = writeFile "sumProduct.py" (show maxSum ++ "\n" ++ show uivarBound ++ "\n" ++ show xivarBound ++ "\n" ++ toPyString phi ++ "\n" ++ toPyString puzzleTau)
