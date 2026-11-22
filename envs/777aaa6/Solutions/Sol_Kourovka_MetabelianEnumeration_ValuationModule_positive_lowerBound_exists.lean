-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.positive_lowerBound_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:56.334838+00:00
-- url     : https://prove2.me/submissions/102d55f8-2356-47f1-8055-f07f6afd1653

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (p : GroupRing Q)
    (hp : ∀ u ∈ p.support, 0 < χ u) : ∃ c, 0 < c ∧ LowerBound χ p c := by
  have hf : ∀ s : Finset Q, (∀ u ∈ s, 0 < χ u) →
      ∃ c : ℝ, 0 < c ∧ ∀ u ∈ s, c ≤ χ u := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨1, by norm_num, by simp⟩
    | @insert u s hu ih =>
      intro h
      obtain ⟨c, hc, hb⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
      refine ⟨min (χ u) c, lt_min (h u (Finset.mem_insert_self _ _)) hc, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb v hv)
  exact hf p.support hp
end Kourovka.MetabelianEnumeration.ValuationModule
