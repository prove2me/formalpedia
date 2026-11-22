-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_top_le_positive_smul
-- name    : Kourovka.MetabelianEnumeration.ValuationModule.top_le_positive_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:40.430806+00:00
-- url     : https://prove2.me/theorems/57558353-382e-4e58-b453-9d43473a6884
-- title:
--   Valuation Module: top le positive smul
-- statement:
--   The Valuation Module construction uses the top le positive smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L90-L100
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ValuationModule.lean#L90-L100

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]

theorem Kourovka.MetabelianEnumeration.ValuationModule.top_le_positive_smul (χ : Q →+ ℝ) (hχ : χ ≠ 0) :
    (⊤ : Submodule (nonnegativeRing χ) M) ≤ positiveIdeal χ • ⊤ := by sorry
