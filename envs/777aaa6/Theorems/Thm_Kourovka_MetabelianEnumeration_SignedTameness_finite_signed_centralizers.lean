-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_finite_signed_centralizers
-- name    : Kourovka.MetabelianEnumeration.SignedTameness.finite_signed_centralizers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:07.867348+00:00
-- url     : https://prove2.me/theorems/ffc4feed-c979-415f-8d78-c2b26125e3c4
-- title:
--   Signed Tameness: finite signed centralizers
-- statement:
--   Compactness converts the directional criterion into a finite signed
--   centralizer family, preserving the action of every selected Laurent polynomial.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/SignedTameness.lean#L61-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/SignedTameness.lean#L61-L75

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Modules_SignedTameness
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SignedTameness
open FiniteCover ConeVerifier ValuationModule TamenessCompactness
variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.SignedTameness.finite_signed_centralizers [Module.Finite (GroupRing (Lattice k)) M]
    (ht : Tame (k := k) M) :
    ∃ ps : List (SignedPolynomial k),
      (∀ p ∈ ps, ∀ m : M, p.2 • m = m) ∧ ConeCover (ps.map signedSupport) := by sorry
