-- Prove2me | solution 1 for mme_released_joint_region0_penalty_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:31:15.132853+00:00
-- url     : https://prove2.me/submissions/e9b71732-ddcc-464b-8288-657dba33af49

import Theorems.Thm_mme_released_joint_interior_penalty_bound
import Theorems.Thm_mme_released_interior_owner0_cell10_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell11_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell12_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell14_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell15_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell18_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell19_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell21_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell22_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell25_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell26_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell27_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell28_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell32_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell36_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner0_cell40_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell10_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell13_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell14_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell15_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell18_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell19_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell21_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell22_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell25_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell26_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell27_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell28_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell32_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell37_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner1_cell40_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell10_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell11_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell12_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell14_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell15_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell18_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell19_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell20_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell21_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell25_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell27_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell32_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell33_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell36_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell37_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner2_cell40_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell10_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell13_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell14_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell15_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell20_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell21_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell22_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell26_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell28_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell31_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell32_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell36_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell37_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner3_cell40_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell10_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell11_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell12_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell15_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell19_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell20_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell21_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell22_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell27_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell31_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell33_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell36_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell37_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner4_cell40_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell10_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell13_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell14_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell15_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell20_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell21_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell22_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell26_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell31_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell33_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell36_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell37_region0_product_dual_penalty
import Theorems.Thm_mme_released_interior_owner5_cell40_region0_product_dual_penalty

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

private def boundNumerator (j : Fin 270) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 414, 1649, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1672, 431, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 400, 1, 0, 0, 0, 1, 0, 1592, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 407, 1, 1, 0, 0, 0, 1564, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1641, 1, 1, 0, 0, 0, 0, 440, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1591, 1, 1, 0, 0, 0, 428, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0] : List ℕ).getD j.val 0

private def bound (j : Fin 270) : ℚ :=
  (boundNumerator j : ℚ) / 1000000000

/-- The full pooled regional penalty has an exact rational upper bound,
normalized by one released outer block. Physical masses are retained. -/
theorem solution :
    penaltyPotential (size 0 1) (splitCount 0 1) ≤
      (denominator : ℝ) ^ 5 * (395 / 1000000000 : ℝ) := by
  have hcases : ∀ j : Fin 270, 0 < size 0 1 j →
      j ∈ ([10, 11, 12, 14, 15, 18, 19, 21, 22, 25, 26, 27, 28, 32, 36, 40, 55, 58, 59, 60, 63, 64, 66, 67, 70, 71, 72, 73, 77, 82, 85, 100, 101, 102, 104, 105, 108, 109, 110, 111, 115, 117, 122, 123, 126, 127, 130, 145, 148, 149, 150, 155, 156, 157, 161, 163, 166, 167, 171, 172, 175, 190, 191, 192, 195, 199, 200, 201, 202, 207, 211, 213, 216, 217, 220, 235, 238, 239, 240, 245, 246, 247, 251, 256, 258, 261, 262, 265] : List (Fin 270)) := by
    decide +kernel
  have h := mme_released_joint_interior_penalty_bound 0 1
    (fun j => (bound j : ℝ)) ?_
  · have hc : (∑ j : Fin 270,
        (size 0 1 j : ℚ) * bound j) ≤
        (denominator : ℚ) ^ 5 * (395 / 1000000000 : ℚ) := by
      decide +kernel
    have hcR := (Rat.cast_le (K := ℝ)).2 hc
    push_cast at hcR
    exact h.trans hcR
  · intro j hj
    have hjcases := hcases j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjcases
    rcases hjcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 10 =>
          (ReleasedInterior.splitWeight 0 10 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell10_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 11 =>
          (ReleasedInterior.splitWeight 0 11 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell11_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 12 =>
          (ReleasedInterior.splitWeight 0 12 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell12_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 14 =>
          (ReleasedInterior.splitWeight 0 14 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell14_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 15 =>
          (ReleasedInterior.splitWeight 0 15 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell15_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 18 =>
          (ReleasedInterior.splitWeight 0 18 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell18_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 19 =>
          (ReleasedInterior.splitWeight 0 19 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell19_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 21 =>
          (ReleasedInterior.splitWeight 0 21 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell21_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 22 =>
          (ReleasedInterior.splitWeight 0 22 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell22_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 25 =>
          (ReleasedInterior.splitWeight 0 25 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell25_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 26 =>
          (ReleasedInterior.splitWeight 0 26 0 c : ℝ) / 1000000000000) ≤
          ((414 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner0_cell26_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 27 =>
          (ReleasedInterior.splitWeight 0 27 0 c : ℝ) / 1000000000000) ≤
          ((1649 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell27_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 28 =>
          (ReleasedInterior.splitWeight 0 28 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell28_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 32 =>
          (ReleasedInterior.splitWeight 0 32 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell32_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 36 =>
          (ReleasedInterior.splitWeight 0 36 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell36_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 40 =>
          (ReleasedInterior.splitWeight 0 40 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner0_cell40_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 10 =>
          (ReleasedInterior.splitWeight 1 10 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell10_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 13 =>
          (ReleasedInterior.splitWeight 1 13 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell13_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 14 =>
          (ReleasedInterior.splitWeight 1 14 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell14_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 15 =>
          (ReleasedInterior.splitWeight 1 15 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell15_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 18 =>
          (ReleasedInterior.splitWeight 1 18 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell18_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 19 =>
          (ReleasedInterior.splitWeight 1 19 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell19_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 21 =>
          (ReleasedInterior.splitWeight 1 21 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell21_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 22 =>
          (ReleasedInterior.splitWeight 1 22 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell22_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 25 =>
          (ReleasedInterior.splitWeight 1 25 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell25_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 26 =>
          (ReleasedInterior.splitWeight 1 26 0 c : ℝ) / 1000000000000) ≤
          ((1672 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner1_cell26_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 27 =>
          (ReleasedInterior.splitWeight 1 27 0 c : ℝ) / 1000000000000) ≤
          ((431 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell27_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 28 =>
          (ReleasedInterior.splitWeight 1 28 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell28_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 32 =>
          (ReleasedInterior.splitWeight 1 32 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell32_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 37 =>
          (ReleasedInterior.splitWeight 1 37 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell37_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 40 =>
          (ReleasedInterior.splitWeight 1 40 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner1_cell40_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 10 =>
          (ReleasedInterior.splitWeight 2 10 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell10_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 11 =>
          (ReleasedInterior.splitWeight 2 11 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell11_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 12 =>
          (ReleasedInterior.splitWeight 2 12 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell12_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 14 =>
          (ReleasedInterior.splitWeight 2 14 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell14_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 15 =>
          (ReleasedInterior.splitWeight 2 15 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell15_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 18 =>
          (ReleasedInterior.splitWeight 2 18 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell18_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 19 =>
          (ReleasedInterior.splitWeight 2 19 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell19_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 20 =>
          (ReleasedInterior.splitWeight 2 20 0 c : ℝ) / 1000000000000) ≤
          ((400 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner2_cell20_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 21 =>
          (ReleasedInterior.splitWeight 2 21 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell21_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 25 =>
          (ReleasedInterior.splitWeight 2 25 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell25_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 27 =>
          (ReleasedInterior.splitWeight 2 27 0 c : ℝ) / 1000000000000) ≤
          ((1592 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner2_cell27_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 32 =>
          (ReleasedInterior.splitWeight 2 32 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell32_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 33 =>
          (ReleasedInterior.splitWeight 2 33 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell33_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 36 =>
          (ReleasedInterior.splitWeight 2 36 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell36_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 37 =>
          (ReleasedInterior.splitWeight 2 37 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell37_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 40 =>
          (ReleasedInterior.splitWeight 2 40 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner2_cell40_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 10 =>
          (ReleasedInterior.splitWeight 3 10 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell10_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 13 =>
          (ReleasedInterior.splitWeight 3 13 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell13_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 14 =>
          (ReleasedInterior.splitWeight 3 14 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell14_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 15 =>
          (ReleasedInterior.splitWeight 3 15 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell15_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 20 =>
          (ReleasedInterior.splitWeight 3 20 0 c : ℝ) / 1000000000000) ≤
          ((407 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell20_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 21 =>
          (ReleasedInterior.splitWeight 3 21 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell21_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 22 =>
          (ReleasedInterior.splitWeight 3 22 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell22_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 26 =>
          (ReleasedInterior.splitWeight 3 26 0 c : ℝ) / 1000000000000) ≤
          ((1564 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner3_cell26_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 28 =>
          (ReleasedInterior.splitWeight 3 28 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell28_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 31 =>
          (ReleasedInterior.splitWeight 3 31 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell31_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 32 =>
          (ReleasedInterior.splitWeight 3 32 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell32_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 36 =>
          (ReleasedInterior.splitWeight 3 36 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell36_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 37 =>
          (ReleasedInterior.splitWeight 3 37 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell37_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 40 =>
          (ReleasedInterior.splitWeight 3 40 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner3_cell40_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 10 =>
          (ReleasedInterior.splitWeight 4 10 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell10_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 11 =>
          (ReleasedInterior.splitWeight 4 11 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell11_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 12 =>
          (ReleasedInterior.splitWeight 4 12 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell12_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 15 =>
          (ReleasedInterior.splitWeight 4 15 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell15_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 19 =>
          (ReleasedInterior.splitWeight 4 19 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell19_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 20 =>
          (ReleasedInterior.splitWeight 4 20 0 c : ℝ) / 1000000000000) ≤
          ((1641 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell20_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 21 =>
          (ReleasedInterior.splitWeight 4 21 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell21_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 22 =>
          (ReleasedInterior.splitWeight 4 22 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell22_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 27 =>
          (ReleasedInterior.splitWeight 4 27 0 c : ℝ) / 1000000000000) ≤
          ((440 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner4_cell27_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 31 =>
          (ReleasedInterior.splitWeight 4 31 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell31_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 33 =>
          (ReleasedInterior.splitWeight 4 33 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell33_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 36 =>
          (ReleasedInterior.splitWeight 4 36 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell36_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 37 =>
          (ReleasedInterior.splitWeight 4 37 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell37_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 40 =>
          (ReleasedInterior.splitWeight 4 40 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner4_cell40_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 10 =>
          (ReleasedInterior.splitWeight 5 10 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell10_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 13 =>
          (ReleasedInterior.splitWeight 5 13 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell13_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 14 =>
          (ReleasedInterior.splitWeight 5 14 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell14_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 15 =>
          (ReleasedInterior.splitWeight 5 15 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell15_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 20 =>
          (ReleasedInterior.splitWeight 5 20 0 c : ℝ) / 1000000000000) ≤
          ((1591 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell20_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 21 =>
          (ReleasedInterior.splitWeight 5 21 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell21_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 22 =>
          (ReleasedInterior.splitWeight 5 22 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell22_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 26 =>
          (ReleasedInterior.splitWeight 5 26 0 c : ℝ) / 1000000000000) ≤
          ((428 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      convert mme_released_interior_owner5_cell26_region0_product_dual_penalty using 1
      norm_num
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 31 =>
          (ReleasedInterior.splitWeight 5 31 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell31_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 33 =>
          (ReleasedInterior.splitWeight 5 33 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell33_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 36 =>
          (ReleasedInterior.splitWeight 5 36 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell36_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 37 =>
          (ReleasedInterior.splitWeight 5 37 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell37_region0_product_dual_penalty
    · subst j
      change Real.log 2 * RecursiveThinSplit.entropyPenalty
        (fun c : ReleasedInterior.Split 40 =>
          (ReleasedInterior.splitWeight 5 40 0 c : ℝ) / 1000000000000) ≤
          ((1 / 1000000000 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      exact mme_released_interior_owner5_cell40_region0_product_dual_penalty


#print axioms solution
