-- Prove2me | solution 1 for mme_dwz_positive_422_original_profile_value_at_ledger_rate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:23:40.900821+00:00
-- url     : https://prove2.me/submissions/a018f736-8a13-4f90-9076-bef588dc4b24

import Theorems.Thm_mme_dwz_positive_422_original_profile_value
import Theorems.Thm_mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
import Definitions.Def_mme_dwz_q5_global_component_ledger_data
import Mathlib.Tactic
open MME.DWZQ5GlobalLedger MME.DWZQ5ExactData
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem solution {K : Type u} [Field K] :
    MME.DWZQ5GlobalLedger.ComponentEndpoint K 32 := by
  have hrQ : componentLogFloor 32 = (3202624804523 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 32 : ℝ) = 3202624804523 / 500000000000 := by
    rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 32) MME.DWZPositiveComponent422.parentProfile 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_422_original_profile_value (K := K))
