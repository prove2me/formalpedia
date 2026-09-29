-- Prove2me | Theorems.Thm_mme_released_global_outer_rate_budget
-- name    : mme_released_global_outer_rate_budget
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T04:01:00.175455+00:00
-- url     : https://prove2.me/theorems/619b205f-0dc1-4d41-953d-1637203e7bdd
-- title:
--   Certified outer rates admit strict extraction gaps
-- statement:
--   The six complete actual outer rate bounds give nonnegative extraction rates strictly below the actual rates. Their sixfold sum retains the stated normalized rate with loss at most one millionth, without assuming numerical rate bounds. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_outer_loss_budget
import Theorems.Thm_mme_released_global_owner0_profile_rate_bound
import Theorems.Thm_mme_released_global_owner1_profile_rate_bound
import Theorems.Thm_mme_released_global_owner2_profile_rate_bound
import Theorems.Thm_mme_released_global_owner3_profile_rate_bound
import Theorems.Thm_mme_released_global_owner4_profile_rate_bound
import Theorems.Thm_mme_released_global_owner5_profile_rate_bound
open scoped BigOperators
open MME MME.ReleasedGlobal

theorem mme_released_global_outer_rate_budget :
    ∃ rho : Fin 6 → ℝ, (∀ owner, 0 ≤ rho owner) ∧
      (∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) ∧
      (6707994429 / 125000000 - 1 / 1000000 : ℝ) ≤ 6 * ∑ owner, rho owner := by sorry
