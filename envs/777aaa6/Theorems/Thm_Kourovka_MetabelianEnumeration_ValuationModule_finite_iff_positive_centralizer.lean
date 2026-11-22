-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_finite_iff_positive_centralizer
-- name    : Kourovka.MetabelianEnumeration.ValuationModule.finite_iff_positive_centralizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:11:23.247147+00:00
-- url     : https://prove2.me/theorems/410a27a2-4ae9-4364-b189-bac77c7d7c8c
-- title:
--   Valuation Module: finite iff positive centralizer
-- statement:
--   Bieri–Strebel's directional centralizer criterion, proved for the actual
--   Laurent module rather than assumed as a certificate field.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L202-L211
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L202-L211

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.ValuationModule.finite_iff_positive_centralizer (χ : Q →+ ℝ) (hχ : χ ≠ 0)
    [Module.Finite (GroupRing Q) M] :
    Module.Finite (nonnegativeRing χ) M ↔
      ∃ p : GroupRing Q, (∀ u ∈ p.support, 0 < χ u) ∧ ∀ m : M, p • m = m := by sorry
