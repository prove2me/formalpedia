-- Prove2me | solution 1 for mme_released_interior_region_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:36:54.919507+00:00
-- url     : https://prove2.me/submissions/d6d9b851-f395-485b-869c-22eed9465ee1

import Theorems.Thm_mme_released_interior_owner0_region_coarse_penalty
import Theorems.Thm_mme_released_interior_owner1_region_coarse_penalty
import Theorems.Thm_mme_released_interior_owner2_region_coarse_penalty
import Theorems.Thm_mme_released_interior_owner3_region_coarse_penalty
import Theorems.Thm_mme_released_interior_owner4_region_coarse_penalty
import Theorems.Thm_mme_released_interior_owner5_region_coarse_penalty

open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

/-- All nonempty regions of the released interior recipes have coarse entropy
minus the maximum-entropy penalty at least two fifths. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (hi : (seed owner s).boundary = [])
    (hn : 0 < (seed owner s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight owner s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s =>
          (splitWeight owner s r c : ℝ) / 1000000000000) := by
  fin_cases owner
  · exact mme_released_interior_owner0_region_coarse_penalty s r hi hn
  · exact mme_released_interior_owner1_region_coarse_penalty s r hi hn
  · exact mme_released_interior_owner2_region_coarse_penalty s r hi hn
  · exact mme_released_interior_owner3_region_coarse_penalty s r hi hn
  · exact mme_released_interior_owner4_region_coarse_penalty s r hi hn
  · exact mme_released_interior_owner5_region_coarse_penalty s r hi hn


#print axioms solution
