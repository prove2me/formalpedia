-- Prove2me | solution 1 for mme_released_joint_compatibility_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:17:07.893589+00:00
-- url     : https://prove2.me/submissions/e307a0c8-f87e-4a87-9425-838aeb5e8ebf

import Theorems.Thm_mme_regional_compatibility_component_sum
import Theorems.Thm_mme_released_joint_zero_size_profile

open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.RecursiveYZ

/-- Bounds for the positive-size parent components bound the actual pooled
compatibility potential. Zero-size labels contribute no entropy. -/
theorem solution (r : Fin 6) (k : ℕ) (i : Fin 2)
    (bound : Fin 270 → ℝ) (hb : ∀ j, 0 ≤ bound j)
    (hc : ∀ j, 0 < size r k j →
      ((∑ c : RecursiveThinSplit.Split 4 (parent r j),
          if yzBoundary i ⟨j, c⟩ then
            massEntropy (fun w ↦ (integerProfile r k (yzMode i) ⟨j, c⟩ w : ℝ)) else 0) +
        ∑ a : Fin 5, massEntropy (fun w ↦
          ∑ c : RecursiveThinSplit.Split 4 (parent r j),
            if ¬ yzBoundary i ⟨j, c⟩ ∧ c.val (yzMode i) = a then
              (integerProfile r k (yzMode i) ⟨j, c⟩ w : ℝ) else 0)) ≤ bound j) :
    compatibilityPotential i (integerProfile r k (yzMode i)) ≤ ∑ j, bound j := by
  rw [mme_regional_compatibility_component_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hz : size r k j = 0
  · have hmu := mme_released_joint_zero_size_profile r k j hz (yzMode i)
    simpa [hmu, massEntropy, entropy] using hb j
  · exact hc j (Nat.pos_of_ne_zero hz)


#print axioms solution
