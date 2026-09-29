-- Prove2me | Theorems.Thm_mme_released_global_owner4_profile_rate_bound
-- name    : mme_released_global_owner4_profile_rate_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:19:25.995976+00:00
-- url     : https://prove2.me/theorems/a8c51d3c-ccb2-40f4-ab4b-f3503cbd2371
-- title:
--   Outer owner 4 has a certified complete rate
-- statement:
--   Certified actual coarse, word, compatibility, and penalty bounds give a lower bound on the minimum of the three complete directional outer rates. Strict extraction gaps and the main exponent conclusion remain separate obligations. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner4_product_dual_penalty
import Theorems.Thm_mme_released_global_owner4_coarse_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode1_word_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode2_word_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode1_compatibility_entropy_bound
import Theorems.Thm_mme_released_global_owner4_mode2_compatibility_entropy_bound
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_profile_rate_bound :
    (1490663626 / 1000000000 : ℝ) ≤ (profile 4).rate (fun _ ↦ 1) := by sorry
