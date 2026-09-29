-- Prove2me | solution 1 for mme_released_joint_interior_penalty_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:54:05.548288+00:00
-- url     : https://prove2.me/submissions/d00bd6e1-07f1-4cde-b1c6-58cfad5440ef

import Theorems.Thm_mme_entropy_penalty_coordinate_equiv
import Definitions.Def_mme_released_joint_interior_profiles
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

/-- Bounds for the actual released split distributions control the pooled
penalty in common mode order, with exact physical masses at every scale. -/
theorem solution
    (r : Fin 6) (k : ℕ) (bound : Fin 270 → ℝ)
    (hb : ∀ j, 0 < size r k j →
      Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split (component j).2 =>
          (ReleasedInterior.splitWeight (component j).1 (component j).2 r c : ℝ) /
            1000000000000) ≤ bound j) :
    penaltyPotential (size r k) (splitCount r k) ≤
      ∑ j, (size r k j : ℝ) * bound j := by
  classical
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : size r k j = 0
  · simp [hz]
  · have hn : 0 < size r k j := Nat.pos_of_ne_zero hz
    have hnR : (0 : ℝ) < size r k j := by exact_mod_cast hn
    have hnorm (c : RecursiveThinSplit.Split 4 (parent r j)) :
        (splitCount r k j c : ℝ) / (size r k j : ℝ) =
        (ReleasedInterior.splitWeight (component j).1 (component j).2 r
          ((splitEquiv r j).symm c) : ℝ) / 1000000000000 := by
      apply (div_eq_iff hnR.ne').2
      unfold splitCount size ReleasedInterior.splitCount ReleasedInterior.regionalSize
        denominator
      push_cast
      ring
    have he := mme_entropy_penalty_coordinate_equiv
      (ReleasedInterior.parent (component j).2 0)
      (orientation (component j).1 r)
      (fun c => (ReleasedInterior.splitWeight (component j).1 (component j).2 r c : ℝ) /
        1000000000000)
    change RecursiveThinSplit.entropyPenalty
      (fun c => (ReleasedInterior.splitWeight (component j).1 (component j).2 r
        ((splitEquiv r j).symm c) : ℝ) / 1000000000000) = _ at he
    simp_rw [hnorm]
    rw [he, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb j hn) hnR.le


#print axioms solution
