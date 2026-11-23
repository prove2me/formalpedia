-- Prove2me | Theorems.Thm_kyprianou82_psi_zero_from_coupling
-- name    : kyprianou82_psi_zero_from_coupling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:32:49.57839+00:00
-- url     : https://prove2.me/theorems/1a55e072-dd77-4946-97fb-fd1b06173871
-- title:
--   Original Laplace exponent vanishes at zero
-- statement:
--   The filtered Avram coupling transfers the source result that the Levy exponent vanishes at zero back to the original Laplace exponent.
-- source:
--   Kyprianou chapter 8 Stage B source result 81 filtered coupling and Levy root domain.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem kyprianou82_psi_zero_from_coupling
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    : ψ 0 = 0 := by
  sorry
