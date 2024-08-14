{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-|
Module      : ToSBV
Description : Transform a program-epistemic validity into a predicate in SBV

The main program 'toSBV' takes the list of variables,
the constraint formula (a 'FOLFormula'), and the target formula
(the translation of a 'ModalFormula' into a 'FOLFormula') 

NOTE: quantifiers are transformed into conjunction/disjunction
because SBV only supports quantifications in Prenex Normal Form

See also the companion paper here https://doi.org/10.48550/arXiv.2206.13841
Maintainer: S.F. Rajaona sfrajaona@gmail.com
-}

module ToSBV where

import Logics
import Data.SBV
import Data.Maybe
import Data.Map (Map, fromList, (!))
import Debug.Trace
import Translation

-- |'toSBV' takes a constraint \(\phi\) (in 'FOLFormula') and target formula in 'FOLFormula'.
-- The target formula is usually the translation of a 'ModalFormula' \(\tau(\ldots)\) via the "Tau" module.
-- Both formulas are converted into SBV formula. Variables are converted into SBV symbolic variables
toSBV :: [Var] -> ModalFormula -> ModalFormula -> Predicate
toSBV vs phi formula = do freeBools      <- symbolics [varName (BVar ags x)  | (BVar ags x)  <- vs] 
                          freeInts       <- symbolics [varName (NVar ags d x)  | (NVar ags d x)  <- vs] 
                          let toFreeBool = fromList $ zip [(BVar ags x)  | (BVar ags x)  <- vs] freeBools
                          let toFreeInt  = fromList $ zip [(NVar ags d x)  | (NVar ags d x)  <- vs] freeInts
                          constrain      $ toSymb (toFreeBool, toFreeInt) phi
                          return         $ toSymb (toFreeBool, toFreeInt) formula
                                    
                                    
                                    
                                    

-- convert a formula into SBV formula
toSymb :: (Map Var SBool, Map Var SInteger) -> ModalFormula -> SBool
toSymb ff (Atom b)              = toSymbBExpr ff b
toSymb ff (Neg alpha)           = sNot (toSymb ff alpha)
toSymb ff (Disj as)             = sOr  [toSymb ff a | a <- as]
toSymb ff (Conj as)             = sAnd [toSymb ff a | a <- as]
toSymb ff (Imp alpha1 alpha2)   = (toSymb ff alpha1) .=>  (toSymb ff alpha2)
toSymb ff (Equiv alpha1 alpha2) = (toSymb ff alpha1) .<=> (toSymb ff alpha2)
-- toSymb ff (ForAllB n f)         = sAll (\z -> toSymb ff (sub (uBVar n) (B z) f)) [True, False]
-- toSymb ff (ExistsB n f)         = sAny (\z -> toSymb ff (sub (eBVar n) (B z) f)) [True, False]
toSymb ff (ForAllB n ags f)         = quantifiedBool (\(Forall z) -> (toSymb ff (sub (uBVar n ags) (BSymb z) f)))
toSymb ff (ExistsB n ags f)         = quantifiedBool (\(Exists z) -> (toSymb ff (sub (eBVar n ags) (BSymb z) f)))
-- toSymb ff (ForAllI n d f)       = sAll (\z -> toSymb ff (sub (uIVar n d) (I z) f)) [(fst d)..(snd d)] 
-- toSymb ff (ExistsI n d f)       = sAny (\z -> toSymb ff (sub (eIVar n d) (I z) f)) [(fst d)..(snd d)]
-- toSymb ff (ForAllI n d f)    = skolemize $ quantifiedBool (\(Forall z) -> (z .< literal (snd d) .&& literal (fst d) .< z) .=>  (toSymb ff (sub (uIVar n d) (ISymb z) f)))
-- toSymb ff (ExistsI n d f)    = skolemize $ quantifiedBool (\(Exists z) -> (z .< literal (snd d) .&& literal (fst d) .< z) .&&  (toSymb ff (sub (eIVar n d) (ISymb z) f)))
toSymb ff (ForAllI n ags d f)    = quantifiedBool (\(Forall z) -> (toSymb ff (sub (uIVar n ags d) (ISymb z) f)))
toSymb ff (ExistsI n ags d f)    = quantifiedBool (\(Exists z) -> (toSymb ff (sub (eIVar n ags d) (ISymb z) f)))

-- | toSymbBExpr: 
-- convert a boolean expression in BExpr into SBV SBool. 
-- variables in the BExpr are replaced by SBV variables created in freeBools
toSymbBExpr :: (Map Var SBool, Map Var SInteger)  -> BExpr -> SBool
toSymbBExpr ff@(freeB,freeI) (B True)     = sTrue
toSymbBExpr ff@(freeB,freeI) (B False)    = sFalse
toSymbBExpr ff@(freeB,freeI) (BSymb z)    = z
toSymbBExpr ff@(freeB,freeI) (BVal x)   = (freeB!x)
toSymbBExpr ff@(freeB,freeI) (Xoor [b])    = toSymbBExpr ff b
toSymbBExpr ff@(freeB,freeI) (Xoor (b:bs)) = toSymbBExpr ff b .<+> toSymbBExpr ff (Xoor bs)
toSymbBExpr ff@(freeB,freeI) (Aand bs)     = sAnd [toSymbBExpr ff b | b <- bs]
toSymbBExpr ff@(freeB,freeI) (Oor bs)      = sOr [toSymbBExpr ff b | b <- bs]
toSymbBExpr ff@(freeB,freeI) (BEq b b')   = toSymbBExpr ff b .== toSymbBExpr ff b'
toSymbBExpr ff@(freeB,freeI) (Eq m n)     = toSymbNExpr freeI m .== toSymbNExpr freeI n
toSymbBExpr ff@(freeB,freeI) (LEq m n)    = toSymbNExpr freeI m .<= toSymbNExpr freeI n


-- | toSymbNExpr: 
-- convert a numerical expression in NExpr into SBV SInteger 
-- variables in the NExpr are replaced by SBV variables created in freeInt
toSymbNExpr :: Map Var SInteger -> NExpr -> SInteger
toSymbNExpr freeI (IVal x) = freeI!x    
toSymbNExpr freeI (ISymb x) = x
toSymbNExpr freeI (I n) = literal n 
toSymbNExpr freeI (Add m n) = toSymbNExpr freeI m + toSymbNExpr freeI n 
toSymbNExpr freeI (Mul m n) = toSymbNExpr freeI m * toSymbNExpr freeI n 
