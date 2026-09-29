-- Prove2me | solution 1 for mme_released_global_owner2_profile_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T02:11:14.118036+00:00
-- url     : https://prove2.me/submissions/ef42da04-4244-4ef6-b1b6-c33478467975

import Theorems.Thm_mme_released_global_owner2_product_dual_penalty
import Theorems.Thm_mme_released_global_owner2_coarse_entropy_bound
import Theorems.Thm_mme_released_global_owner2_mode1_word_entropy_bound
import Theorems.Thm_mme_released_global_owner2_mode2_word_entropy_bound
import Theorems.Thm_mme_released_global_owner2_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_global_owner2_mode2_compatibility_entropy_bound

open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The minimum of the three complete actual outer rates retains a
certified rational lower bound. -/
theorem solution :
    (1490666224 / 1000000000 : ℝ) ≤ (profile 2).rate (fun _ ↦ 1) := by
  have hc0 := mme_released_global_owner2_coarse_entropy_bound 0
  change (1490681393 / 1000000000 : ℝ) ≤ (profile 2).coarse 0 0 at hc0
  have hc1 := mme_released_global_owner2_coarse_entropy_bound 1
  change (1489865157 / 1000000000 : ℝ) ≤ (profile 2).coarse 1 0 at hc1
  have hc2 := mme_released_global_owner2_coarse_entropy_bound 2
  change (1488365079 / 1000000000 : ℝ) ≤ (profile 2).coarse 2 0 at hc2
  have hp := mme_released_global_owner2_product_dual_penalty
  change Real.log 2 * MME.RecursiveThinSplit.entropyPenalty ((profile 2).1 0) ≤
    (15169 / 1000000000 : ℝ) at hp
  have hw1 := mme_released_global_owner2_mode1_word_entropy_bound
  have hk1 := mme_released_global_owner2_mode1_compatibility_entropy_bound
  have hw2 := mme_released_global_owner2_mode2_word_entropy_bound
  have hk2 := mme_released_global_owner2_mode2_compatibility_entropy_bound
  simp only [GlobalCW.EntropyProfile.rate, Fin.sum_univ_one, one_mul]
  refine le_min ?_ (le_min ?_ ?_) <;> nlinarith


#print axioms solution
