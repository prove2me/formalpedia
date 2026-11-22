-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_positive_centralizer_of_finite
-- name    : Kourovka.MetabelianEnumeration.ValuationModule.positive_centralizer_of_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:22.003001+00:00
-- url     : https://prove2.me/theorems/e4915aa5-b60d-4b58-9885-c5f24ad51026
-- title:
--   Valuation Module: positive centralizer of finite
-- statement:
--   The positive-centralizer half of Bieri–Strebel Proposition 2.1, for the
--   actual group ring and its support-defined valuation subring.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L104-L110
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L104-L110

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.ValuationModule.positive_centralizer_of_finite (χ : Q →+ ℝ) (hχ : χ ≠ 0)
    [Module.Finite (nonnegativeRing χ) M] :
    ∃ p : GroupRing Q, (∀ u ∈ p.support, 0 < χ u) ∧ ∀ m : M, p • m = m := by sorry
