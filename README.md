# program-epistemic-logic-2-smt
Verifying Properties of Knowledge-Based Programs with SMT Solvers (SEFM 2022)

This repo contains:
1) Haskell translator (Logic.hs and Translation.hs): implements the function tau which transforms
a program-epistemic validity into first-order validity 

2) SBV solver (ToSBV.hs): transforms the translated formula (and context phi)
into an SBV predicate (Not very efficient because SBV currently supports f-o formula in Prenex form, and most of our translated formulas have nested quantifications.) 

3) Examples:
- Dining Cryptographers: The translated formula is directly encoded in z3dc.py.
 The SP-based translation used for comparison (i.e. Gorogiannis et al 2017) is encoded in z3dcSP.py.

- Cheryl's Birthday puzzle:
There are two options 
  - solve directly in Haskell via the SBV solver (see ExampleCherylsBirthday.hs)  

  - generate the first order formula from the Haskell translator (ExampleCherylsBirthday.hs) then call another SMT API (e.g. z3cherylsBirthday.py) to solve the formula from the output file.
