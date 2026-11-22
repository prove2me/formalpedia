-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_finite_of_positive_centralizer
-- name    : Kourovka.MetabelianEnumeration.ValuationModule.finite_of_positive_centralizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:59.119021+00:00
-- url     : https://prove2.me/theorems/69856c83-d1b4-4588-ae9a-59ed6268f5c2
-- title:
--   Valuation Module: finite of positive centralizer
-- statement:
--   The converse direction preserves any chosen finite generating family.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L192-L198
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L192-L198

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.ValuationModule.finite_of_positive_centralizer (χ : Q →+ ℝ) [Module.Finite (GroupRing Q) M]
    (p : GroupRing Q) (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m) :
    Module.Finite (nonnegativeRing χ) M := by sorry
