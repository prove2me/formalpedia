-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_positive_signed_support
-- name    : Kourovka.MetabelianEnumeration.SignedTameness.positive_signed_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:15.631829+00:00
-- url     : https://prove2.me/theorems/b9894ecf-0a1c-449d-9b8f-823d2301e0b0
-- title:
--   Signed Tameness: positive signed support
-- statement:
--   The Signed Tameness construction uses the positive signed support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/SignedTameness.lean#L45-L50
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/SignedTameness.lean#L45-L50

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Modules_SignedTameness
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SignedTameness
open FiniteCover ConeVerifier ValuationModule TamenessCompactness
variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.SignedTameness.positive_signed_support {x : Fin k → ℝ} (p : GroupRing (Lattice k))
    (hp : ∀ u ∈ p.support, 0 < character x u) :
    ∀ u ∈ signedSupport (true, p), 0 < dot u x := by sorry
