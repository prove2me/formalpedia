-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.finite_iff_positive_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:33.988006+00:00
-- url     : https://prove2.me/submissions/5f48de0d-8b2f-4255-9f4c-8238d8551471

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_positive_centralizer_of_finite
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_finite_of_positive_centralizer

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (hχ : χ ≠ 0)
    [Module.Finite (GroupRing Q) M] :
    Module.Finite (nonnegativeRing χ) M ↔
      ∃ p : GroupRing Q, (∀ u ∈ p.support, 0 < χ u) ∧ ∀ m : M, p • m = m := by
  constructor
  · intro h
    letI := h
    exact positive_centralizer_of_finite χ hχ
  · rintro ⟨p, hp, hact⟩
    exact finite_of_positive_centralizer χ p hp hact
end Kourovka.MetabelianEnumeration.ValuationModule
