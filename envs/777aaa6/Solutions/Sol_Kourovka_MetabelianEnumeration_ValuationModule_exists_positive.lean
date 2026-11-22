-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.exists_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:23.447394+00:00
-- url     : https://prove2.me/submissions/ca82e838-ee19-4d94-aa41-0d81d8477540

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
omit [DecidableEq Q]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (hχ : χ ≠ 0) : ∃ q, 0 < χ q := by
  have h : ∃ q, χ q ≠ 0 := by
    by_contra! h
    apply hχ
    ext q
    exact h q
  obtain ⟨q, hq⟩ := h
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact ⟨-q, by simpa using neg_pos.mpr hq⟩
  · exact ⟨q, hq⟩
end Kourovka.MetabelianEnumeration.ValuationModule
