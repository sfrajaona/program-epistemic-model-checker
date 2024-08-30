module ExampleMrSumMrProduct where
import Data.Map as M
import Data.SBV
import Data.List as L
import Logics
import ToSBV
import Translation
import Data.Typeable (typeOf) 


--------------------------
-- AGENTS and VARIABLES --
--------------------------
s :: Agent 
s = Agent "Sum"
p :: Agent 
p = Agent "Product"
m :: Var
m = NVar [s, p] (2,62) ("m")
n :: Var
n = NVar [s, p] (2,62) ("n")
theSum :: Var
theSum = NVar [p] (2,62) ("theSum")
theProd :: Var
theProd = NVar [s] (2,961) ("theProduct")

char2var :: String -> Var
char2var "m" = m
char2var "n" = n
char2var "theSum" = theSum
char2var "theProduct" = theProd

allVars = [theSum,theProd,m,n] 


observables :: Agent -> [Var]
observables a = L.filter (\v -> not (a `elem` varNonObs v)) allVars

-- we work on a single observable var at the moment
observable :: Agent -> Var
observable a = head $ observables a
-----------------------------------------------------
-- Constraint Phi
-----------------------------------------------------
phi :: ModalFormula
phi = Conj [
            Atom (IVal n ≤ IVal m),
            Atom (I 2 ≤ IVal n),
            Atom (IVal theSum ≤ I 62),
            Atom (IVal theSum ≡ (IVal m ∔ IVal n)),
            Atom (IVal theProd ≡ (IVal m ⨰ IVal n))
           ]

-------------------------------------
-- Program C, Weakest Precondition --
-------------------------------------
sumDK = Neg (KV s m) 
prodDK = Neg (KV p m)
sumKprodDK = K s (Neg (KV p m)) 
pK = (KV p m) 
sK = (KV s m) 

combineDict :: Ord a => [M.Map a b] -> (M.Map a b) 
combineDict []  = M.empty 
combineDict (d:ds) = d `M.union` (combineDict ds)  

-- modelSol alpha = combineDict [head [a | a <- enum' pval alpha] | pval <- [2..20] ] 
--
mySolver = z3

spAllSat alpha =  allSatWith mySolver (toSBV [m, n, theSum, theProd] phi (tau phi alpha))

enum pval alpha =  allSatWith mySolver (toSBV [m, n, theSum, theProd] (phi ∧ Atom (IVal theProd ≡ I pval)) (tau phi alpha))

enum' pval alpha = do res <- allSatWith mySolver (toSBV [m, n, theSum, theProd] (phi ∧ Atom (IVal theProd ≡ I pval)) (tau phi alpha))
                      return $ getModelDictionaries res


-- | get all the sat of a formula alpha (involing only K_a or KV_a), by fixing the value of the variable observable by a
-- now it works only for one visible variable per agent, but this can be geeralised to many visible variables by one agent 
--
getSatFixVis ag ϕ alpha = getSatFixVis' (varDomRange theVar) ϕ alpha
  where
    theVar = observable ag
    getSatFixVis' [] ϕ alpha = do 
      return $ [] 
    getSatFixVis' (pval:pvals) ϕ  alpha = do 
      res <- allSatWith mySolver (toSBV [m, n, theSum, theProd] (ϕ ∧ Atom (IVal theVar ≡ I pval)) (tau ϕ alpha))
      resAll <- getSatFixVis' pvals ϕ alpha
      return $ (getModelDictionaries res ++ resAll)

updatePhi ag ϕ alpha = do
  modelDicts <- getSatFixVis ag ϕ alpha
  let newPhi = Disj [Conj [Atom (IVal (char2var i) ≡ I (fromCV (dic M.! i))) | i <- ["m","n", "theProduct", "theSum"]  ] | dic <- modelDicts] 
  return $ newPhi


phiTwo' = do 
  phiOne <- updatePhi p phi (Neg (KV p m)) 
  res <- updatePhi s phiOne (K s (Neg (KV p m)))
  return $ res 

theSolution = do
  phiOne <- updatePhi p phi (Neg (KV p m))
  phiTwo <- updatePhi s phiOne (K s (Neg (KV p m)))
  phiThree <- updatePhi p phiTwo (KV p m) 
  phiFour <- updatePhi p phiThree (KV s m) 
  return phiFour

spAllSat' alpha =  do res <- allSatWith mySolver (toSBV [m, n, theSum, theProd] phi (tau phi alpha))
                      return $ extractModels res
