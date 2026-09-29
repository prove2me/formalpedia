-- Prove2me | solution 1 for mme_partition_mass_entropy_full_sum
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:16.233981+00:00
-- url     : https://prove2.me/submissions/5c40ef97-9307-4ee0-8195-d2e1fc2fdeb1

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Definitions.Def_mme_recursive_yz_compatibility

open scoped BigOperators
open MME.RegionRate MME.RecursiveYZ

/-- Boundary partition entropy can be summed over all cells by inserting
zero masses for nonboundary cells. The full index type is computable. -/
theorem solution
    {C G W : Type*} [Fintype C] [Fintype G] [Fintype W]
    (boundary : C → Prop) [DecidablePred boundary] [DecidableEq G]
    (group : C → G) (mu : C → W → ℕ) (n : ℕ) :
    let a : C ⊕ G → W → ℕ := fun t w => match t with
      | Sum.inl c => if boundary c then mu c w else 0
      | Sum.inr g => ∑ c, if ¬ boundary c ∧ group c = g then mu c w else 0
    (∑ t, massEntropy (fun w => (partCount boundary group mu t w : ℝ) / n)) =
      ∑ t, massEntropy (fun w => (a t w : ℝ) / n) := by
  intro a
  simp only [Fintype.sum_sum_type, partCount, a]
  congr 1
  · have hterm (c : C) :
        massEntropy (fun w => ((if boundary c then mu c w else 0 : ℕ) : ℝ) / n) =
          if boundary c then massEntropy (fun w => (mu c w : ℝ) / n) else 0 := by
      by_cases hc : boundary c
      · simp [hc]
      · simp [hc, massEntropy, entropy]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter boundary) (by simp)
      (fun c => massEntropy (fun w => (mu c w : ℝ) / n))).symm
  · apply Finset.sum_congr rfl
    intro g hg
    congr 1
    funext w
    congr 2
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h : ¬ boundary c ∧ group c = g <;> simp [h]


#print axioms solution
