-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.finite_of_positive_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:46.31734+00:00
-- url     : https://prove2.me/submissions/5adaef98-727a-4430-8b3d-2016e00b7743

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_span_eq_half_span

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) [Module.Finite (GroupRing Q) M]
    (p : GroupRing Q) (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m) :
    Module.Finite (nonnegativeRing χ) M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := GroupRing Q) (M := M)
  refine ⟨s, top_unique ?_⟩
  intro m _
  exact span_eq_half_span χ p hp hact s m (by rw [hs]; trivial)
end Kourovka.MetabelianEnumeration.ValuationModule
