{-|
Module      : ExampleDiningCryptographers
Description : Implementation  of Chaum's Dining Cryptographers algorithm
Copyright   :
License     : 
Maintainer  : Anonymous
Portability : 
Stability   : 

@n@ agents dine at a round table [Chaum, 1988]. 
The dinner may have been paid by their employer (the NSA), or by one of the agents. 
They execute a protocol to reveal whether one of the agents paid, but without revealing which one. 
The protocol supplies each pair of adjacent agents with a random coin, which can be observed only by that pair. Each agent announces the result of XORing three Booleans: the two coins observable by her and the status of whether she paid for the dinner. The XOR of all announcements is proven to be equal to the disjunction of whether any agent paid.

Dining Cryptographers: The translated formula is directly encoded in z3dc.py. The SP-based translation used for comparison (i.e. Gorogiannis et al 2017) is encoded in z3dcSP.py.
-}
module ExampleDiningCryptographers where
import Data.Map (Map, fromList, (!))
import Data.SBV
import Data.List
import Logics
import Translation
import ToSBV
import Data.Maybe

-- | @ag i@ characterised by its identity @i@ and its nonobservable variables
ag :: Int -> Agent
ag i = Agent (show i)
-- ag i = Agent {identity= show i, nonobs=(allVars\\(obs i))} 

-- | all variables
allVars :: [Var]
allVars = [varx] ++ concat [[varc i, varp i] | i <- [0 .. (n-1)]] 

-- | all agents
allAgents :: [Agent]
allAgents = [ag i | i <- [0 .. (n-1)]]

-- | observability function, \(ag_i\) observes \(x, p_i, c_i, c_{i+1 \mod n}\), 
obs :: Int -> [Var]
obs i = [varx, varp i, varc i, varc $ (i+1) `mod` n] 

-- | boolean variable \(x\)
varx :: Var
varx = BVar [] "x"  -- observable to all

-- | boolean expression x
x :: BExpr
x = BVal varx

-- | boolean variable \(c_i\) coin flip between agent i and agent i-1
varc :: Int -> Var
varc i = BVar (allAgents\\[ag i, ag (i+1 `mod` n) ]) ("c" ++ show i) 

-- | boolean variable \(p_i\) agent i paid
varp :: Int -> Var
varp i = BVar (allAgents\\[ag i]) ("p" ++ show i) 

-- | boolean expression \(p_i\)
p :: Int -> BExpr
p i = BVal $ varp i
 
-- | boolean expression \(c_i\)
c :: Int -> BExpr
c i = BVal $ varc i


-- | \(\phi\) or \(I\) the constraint on the inital states: "that all agents knows that at most one agent paid"
phi :: ModalFormula 
phi = Conj [ Imp (Atom (p i)) (Conj [ Neg (Atom (p j)) | j <- ([0 .. i-1] ++ [i+1 ..  (n-1)])]) | i <- [0 .. (n-1)] ] 

-- | the boolean expression to be assigned to \(x\) in the algorithm
bexprDC :: BExpr
bexprDC = Xoor [Xoor [p i, c i, c $ (i+1) `mod` n] | i <- [0 .. (n-1)]]

-- | the DC algorithm as an assignment to \(x\)
progDC :: Prog              
progDC = BAssign varx bexprDC 

-- | the number of agents
n :: Int 
n = 10 

noonepaid :: ModalFormula 
noonepaid = Conj [Neg (Atom (p i)) | i <- [0 .. (n-1)]]

dontknowwhopaid :: Agent -> ModalFormula
dontknowwhopaid ag = Conj [Neg (K ag (Atom (p j))) | j <- [0 .. (n-1)]] 

alpha1 :: ModalFormula
alpha1 = Imp (Neg (Atom (p 0))) (Disj [K (ag 0) noonepaid, dontknowwhopaid (ag 0)])  

-- | an example of Modal Formula to be verified at the end of the DC algorithm
alpha2 :: ModalFormula
alpha2 = K (ag 0) (Equiv (Atom x) (Disj [Atom (p i) | i <- [0 .. (n-1) ]]))

-- | an example of Modal Formula to be verified at the end of the DC algorithm
alpha3 :: ModalFormula
alpha3 = K (ag 0) (Atom (p 1))  


-- | proving \([progDC] \alpha_1\)
dcAlpha1    = prove $ toSBV allVars phi (tau phi (Box progDC alpha1))

-- | proving \([progDC] \alpha_2\)
dcAlpha2    = prove $ toSBV allVars phi (tau phi (Box progDC alpha2))
-- -- ^
-- DC with \(\alpha_2\) as in IJCAI paper
--
-- >>> prove dcAlpha2
-- Q.E.D.

-- | proving \([progDC] \alpha_3\) (should be falsified) 
dcAlpha3    = prove $ toSBV allVars phi (tau phi (Box progDC alpha3))
-- ^
-- DC with \(\alpha_3\) as in IJCAI paper
--
-- >>> prove dcAlpha3
-- Falsifiable. Counter-example:
--   x  = False :: Bool
--   c0 = False :: Bool
--   c1 = False :: Bool
--   p0 = False :: Bool
--   p1 = False :: Bool
--

