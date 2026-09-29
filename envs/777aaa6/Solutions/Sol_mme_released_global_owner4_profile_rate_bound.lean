-- Prove2me | solution 1 for mme_released_global_owner4_profile_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T03:20:07.0575+00:00
-- url     : https://prove2.me/submissions/7aee11bb-89c2-400a-8311-9e87b1eeb410

import Theorems.Thm_mme_released_global_owner4_product_dual_penalty
import Theorems.Thm_mme_released_global_owner4_coarse_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode1_word_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode2_word_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode2_compatibility_entropy_bound

open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The minimum of the three complete actual outer rates retains a
certified rational lower bound. -/
theorem solution :
    (1490663626 / 1000000000 : ℝ) ≤ (profile 4).rate (fun _ ↦ 1) := by
  have hc0 := mme_released_global_owner4_coarse_entropy_bound 0
  change (1490678804 / 1000000000 : ℝ) ≤ (profile 4).coarse 0 0 at hc0
  have hc1 := mme_released_global_owner4_coarse_entropy_bound 1
  change (1489860946 / 1000000000 : ℝ) ≤ (profile 4).coarse 1 0 at hc1
  have hc2 := mme_released_global_owner4_coarse_entropy_bound 2
  change (1488368546 / 1000000000 : ℝ) ≤ (profile 4).coarse 2 0 at hc2
  have hp := mme_released_global_owner4_product_dual_penalty
  change Real.log 2 * MME.RecursiveThinSplit.entropyPenalty ((profile 4).1 0) ≤
    (15178 / 1000000000 : ℝ) at hp
  have hw1 := mme_released_global_owner4_mode1_word_entropy_bound
  have hk1 := mme_released_global_owner4_mode1_compatibility_entropy_bound
  have hw2 := mme_released_global_owner4_mode2_word_entropy_bound
  have hk2 := mme_released_global_owner4_mode2_compatibility_entropy_bound
  simp only [GlobalCW.EntropyProfile.rate, Fin.sum_univ_one, one_mul]
  refine le_min ?_ (le_min ?_ ?_) <;> nlinarith


#print axioms solution
