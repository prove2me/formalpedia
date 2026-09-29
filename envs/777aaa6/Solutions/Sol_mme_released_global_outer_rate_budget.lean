-- Prove2me | solution 1 for mme_released_global_outer_rate_budget
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T04:01:29.314085+00:00
-- url     : https://prove2.me/submissions/ee51d4fe-0406-4f07-b82d-9486b82d9d0f

import Theorems.Thm_mme_released_global_outer_loss_budget
import Theorems.Thm_mme_released_global_owner0_profile_rate_bound
import Theorems.Thm_mme_released_global_owner1_profile_rate_bound
import Theorems.Thm_mme_released_global_owner2_profile_rate_bound
import Theorems.Thm_mme_released_global_owner3_profile_rate_bound
import Theorems.Thm_mme_released_global_owner4_profile_rate_bound
import Theorems.Thm_mme_released_global_owner5_profile_rate_bound

open scoped BigOperators
open MME MME.ReleasedGlobal

/-- The six certified actual outer rates admit strict extraction gaps
with a total normalized loss of at most one millionth. -/
theorem solution :
    ∃ rho : Fin 6 → ℝ, (∀ owner, 0 ≤ rho owner) ∧
      (∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) ∧
      (6707994429 / 125000000 - 1 / 1000000 : ℝ) ≤ 6 * ∑ owner, rho owner := by
  apply mme_released_global_outer_loss_budget
  intro owner
  fin_cases owner
  · exact mme_released_global_owner0_profile_rate_bound
  · exact mme_released_global_owner1_profile_rate_bound
  · exact mme_released_global_owner2_profile_rate_bound
  · exact mme_released_global_owner3_profile_rate_bound
  · exact mme_released_global_owner4_profile_rate_bound
  · exact mme_released_global_owner5_profile_rate_bound


#print axioms solution
