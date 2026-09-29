-- Prove2me | solution 1 for mme_dwz_q5_fourth_value_240101_over_100_of_component_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:18:36.070508+00:00
-- url     : https://prove2.me/submissions/ce43da78-cac0-4d6b-a06e-5c837fb8c394

import Theorems.Thm_mme_dwz_q5_global_extraction_rate_strict_lower_bound
import Theorems.Thm_mme_dwz_q5_fourth_value_from_prescribed_component_rates
import Theorems.Thm_mme_dwz_fourth_terminal_log_margin
import Definitions.Def_mme_dwz_q5_global_component_ledger_data
import Mathlib.Tactic

open MME MME.DWZRestrictedValue MME.DWZQ5ExactData MME.DWZQ5AsymptoticData
open MME.DWZQ5GlobalLedger
open BigOperators
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

-- The extraction-rate hypothesis is discharged by the numerical proof before publication.
theorem concrete_value {K : Type u} [Field K]
    (hrate : (14905135 / 10000000 : ℝ) < extractionRate)
    (h : AllComponentEndpoints K) :
    HasSixSymmetricTauValueAtLeast (MME.StothersFourth.cwFourthObj K 5)
      (790643 / 1000000) (240101 / 100 : ℝ) := by
  have hnumQ : (155673 / 20000 : ℚ) < 14905135 / 10000000 +
      (∑ c : Fin 45, (component c : ℚ) * componentLogFloor c) / (scale : ℚ) := by
    decide +kernel
  have hnum : (155673 / 20000 : ℝ) < 14905135 / 10000000 +
      (∑ c : Fin 45, (component c : ℝ) * (componentLogFloor c : ℝ)) / (scale : ℝ) := by
    have hq := (Rat.cast_lt (K := ℝ)).2 hnumQ
    push_cast at hq
    exact hq
  have hlog : Real.log (240101 / 100 : ℝ) < (155673 / 20000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    exact mme_dwz_fourth_terminal_log_margin _ (by norm_num [MME.DWZFourthScalar.naturalRateFloor])
  have hv := mme_dwz_q5_fourth_value_from_prescribed_component_rates
    (K := K) (790643 / 1000000) (14905135 / 10000000)
    (Real.log (240101 / 100)) (fun c => (componentLogFloor c : ℝ))
    (by norm_num) hrate (hlog.trans hnum) h
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 240101 / 100)] using hv

theorem solution {K : Type u} [Field K]
    (h : AllComponentEndpoints K) :
    HasSixSymmetricTauValueAtLeast (MME.StothersFourth.cwFourthObj K 5)
      (790643 / 1000000) (240101 / 100 : ℝ) := by
  exact concrete_value mme_dwz_q5_global_extraction_rate_strict_lower_bound h
