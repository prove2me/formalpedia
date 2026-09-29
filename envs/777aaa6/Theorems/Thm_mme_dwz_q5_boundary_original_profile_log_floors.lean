-- Prove2me | Theorems.Thm_mme_dwz_q5_boundary_original_profile_log_floors
-- name    : mme_dwz_q5_boundary_original_profile_log_floors
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:53:14.091037+00:00
-- url     : https://prove2.me/theorems/df773457-e3e9-47e1-9a55-478832f73a8d
-- title:
--   Exact logarithmic bounds for the 17 original X/Y-boundary profiles
-- statement:
--   For each original global component whose X or Y grade is zero, its required ledger logarithmic floor is at most tau times the exact prescribed-Z word-dimension rate.
-- source:
--   Canonical fourth CW basis and released original q=5 DWZ global Z-profile data.

import Definitions.Def_mme_CW_q5_fourth_boundary_alphabet_data
import Definitions.Def_mme_dwz_q5_global_component_ledger_data
open MME.CWFourthBoundaryQ5 MME.DWZQ5GlobalLedger MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
set_option autoImplicit false

theorem mme_dwz_q5_boundary_original_profile_log_floors (c : Fin 45)
    (hc : coarseAddress c 0 = 0 ∨ coarseAddress c 1 = 0) :
    (componentLogFloor c : ℝ) ≤
      (790643 / 1000000 : ℝ) * logDimension (coarseAddress c 2) (rawProfile c)  := by sorry
