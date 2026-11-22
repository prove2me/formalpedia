-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_finite_realizing_polynomials
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.finite_realizing_polynomials
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:20.095286+00:00
-- url     : https://prove2.me/theorems/04b51c29-c34e-4346-b268-7f31cbecec01
-- title:
--   Module Realization: finite realizing polynomials
-- statement:
--   Actual tameness of the Laurent module gives finite group polynomial
--   relations and the exact real cone-cover condition needed by the finite cover.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L100-L112
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L100-L112

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.finite_realizing_polynomials [Module.Finite (GroupRing (Lattice k)) M]
    (j : Multiplicative M →* G) (t : Fin k → G) (h : ActionCompatible j t)
    (ht : Tame (k := k) M) :
    ∃ ps : List (Polynomial k),
      (∀ p ∈ ps, ∀ m : M, j (Multiplicative.ofAdd m) =
        polynomialWord t (j (Multiplicative.ofAdd m)) p) ∧
      ConeVerifier.ConeCover (ps.map polynomialSupport) := by sorry
