{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fbang-patterns#-}
{-|
Module      : Translation
Description : Defines the translation \(\tau\) of a \(\mathcal{L}_{\square K}\) formula
into a \(\mathcal{L}_{FO}\) formula
PLEASE Note that the following translation tau by-pass weakest preconditions
and does not use public announcement formula, since [β]α = {β?}α  

See also the companion paper here https://doi.org/10.48550/arXiv.2206.13841
Maintainer: S.F. Rajaona sfrajaona@gmail.com
-}
module Translation (tau, tauSP, mkExists)  where
import Logics
import qualified Data.List as L 
import Debug.Trace 

---------------------------------
-- | The translation function @tau@
-- in IJCAI17
---------------------------------
tauSP :: ModalFormula -> Formula a -> ModalFormula
tauSP phi (Atom p)              = Atom p
tauSP phi (Neg alpha)           = Neg (tauSP phi alpha)
tauSP phi (Conj as)             = Conj [tauSP phi a | a <- as]
tauSP phi (Disj as)             = Disj [tauSP phi a | a <- as]
tauSP phi (Imp alpha1 alpha2)   = tauSP phi alpha1 ⇒ tauSP phi alpha2
tauSP phi (Equiv alpha1 alpha2) = tauSP phi alpha1 ⇔ tauSP phi alpha2
tauSP phi (K ag alpha)          = mkForAll (L.nub $ concatMap (nonObs ag) [phi,alpha]) (phi ⇒ tauSP phi alpha)


---------------------------------
-- | The translation function @tau@
-- takes the constraint formula in 'FOLFormula' and a
-- target formula in 'ModalFormula'
---------------------------------
tau :: ModalFormula -> Formula a -> ModalFormula
tau phi (Atom p)               = Atom p
tau phi (Neg alpha)            = Neg (tau phi alpha)
tau phi (Conj as)              = Conj [tau phi a | a <- as]
tau phi (Disj as)              = Disj [tau phi a | a <- as]
tau phi (Imp alpha1 alpha2)    = tau phi alpha1 ⇒ tau phi alpha2
tau phi (Equiv alpha1 alpha2)  = (tau phi (alpha1 ⇒ alpha2)) ∧ (tau phi (alpha2 ⇒ alpha1))
-- TODO: nonobs ag ∩ freeVars (alpha)? 
tau phi (K ag alpha)           = mkForAll (L.nub $ concatMap (nonObs ag) [phi,alpha]) (phi ⇒ tau phi alpha)
tau phi (KV a (NVar ags dom v))    = existsI [] dom (\z -> tau phi (K a (Atom (IVal (NVar ags dom v) ≡ IVal z)))) 
tau phi (KVe a (NVar ags dom v))   = forAllI [] dom (\z -> tau phi ((Atom (IVal (NVar ags dom v) ≡ IVal z)) ⇒ K a (Atom (IVal (NVar ags dom v) ≡ IVal z))))  
tau phi (NegKVe a (NVar ags dom v))= forAllI [] dom (\z -> tau phi (Atom (IVal (NVar ags dom v) ≡ IVal z) ⇒ Neg (K a (Atom (IVal (NVar ags dom v) ≡ IVal z)))))
tau phi (Ann beta alpha)       = tau phi beta ⇒ tau (phi ∧ (tau phi beta)) alpha
-- direct translation for assume and assert, without wp, for performance
tau phi (Box (Assume beta) alpha)     = tau phi (Ann beta alpha) 
tau phi (Box (Assert beta) alpha)     = tau phi beta ∧ tau phi (Ann beta alpha)
tau phi (Box p alpha)          = tau phi (wp alpha p)  
-- tau phi (Box (BAssign x e) alpha)     = forAllB (\k -> tau phi (Ann (Atom (BEq (BVal k) e)) (sub x (BVal k) alpha)))
-- tau phi (Box (NAssign x e) alpha)     = forAllI (varDom x) (\k -> tau phi (Ann (Atom (Eq (IVal k) e)) (sub x (IVal k) alpha)))
-- tau phi (Box (Sequence [p]) alpha)    = tau phi (Box p alpha)
-- tau phi (Box (Sequence (p:ps)) alpha) = tau phi (Box p (Box (Sequence ps) alpha))
-- tau phi (Box (Nondet ps) alpha)       = Conj [tau phi (Box p alpha) | p <- ps ]
tau phi (ForAllB n ags alpha)      = ForAllB n ags (tau phi alpha)  
tau phi (ExistsB n ags alpha)      = ExistsB n ags (tau phi alpha)  
tau phi (ForAllI n ags d alpha)    = ForAllI n ags d (tau phi alpha)  
tau phi (ExistsI n ags d alpha)    = ExistsI n ags d (tau phi alpha)  

-- | 'mkForAll' writes 'Forall' for a vector  of variables.
--    Note that 'mkForAll' uses 'forAllB', 
--    which is still another constructor for 'ForAllB',
--    'forAllB' takes care of variable binding, 
mkForAll :: [Var] -> ModalFormula -> ModalFormula
mkForAll [] f          = f
mkForAll [BVar ags x] f    = forAllB ags (\z -> sub (BVar ags x) (BVal z) $! f)
mkForAll ((BVar ags x):xs) f = let body = (mkForAll xs $! f) in
                         forAllB ags (\z -> sub (BVar ags x) (BVal z) $! body)
mkForAll [NVar ags dom x] f    = forAllI ags dom (\z -> sub (NVar ags dom x) (IVal z) $! f)
mkForAll ((NVar ags dom x):xs) f = let body = (mkForAll xs $! f) in
                         forAllI ags dom (\z -> sub (NVar ags dom x) (IVal z) $! body)


-- | 'mkForExists' writes 'Exists' for a vector (list) of variables.
-- Note that 'mkForExists' uses 'existsB', which is still another constructor for 'Exists',
-- 'existsB' takes care of variable name binding
---------------------------------------------
mkExists :: [Var] -> ModalFormula -> ModalFormula
mkExists [] f          = f
mkExists [BVar ags x] f    = existsB ags (\z -> sub (BVar ags x) (BVal z) f)
mkExists (BVar ags x:xs) f = existsB ags (\z -> sub (BVar ags x) (BVal z) (mkExists xs f))
mkExists [NVar ags dom x] f= existsI ags dom (\z -> sub (NVar ags dom x) (IVal z) f)
mkExists (NVar ags dom x:xs) f = existsI ags dom (\z -> sub (NVar ags dom x) (IVal z) (mkExists xs f))
