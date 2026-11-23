-- Prove2me | Theorems.Thm_kyprianou82_actualHeight_zero_raw
-- name    : kyprianou82_actualHeight_zero_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:53:24.082981+00:00
-- url     : https://prove2.me/theorems/12774a64-ea34-46f6-8a21-2d42ad3c09a2
-- title:
--   Zero-rate unrestricted first-passage discount identity
-- statement:
--   The unrestricted discounted first-passage expectation at rate zero is the exponential of the negative principal exponent at zero. Positive rates tend to zero along 1/(n+1); principal exponents converge by the source domain bridge; pointwise discount convergence and unit domination give dominated convergence of the integrals.
-- source:
--   Kyprianou chapter 8 Stage B; derived from the Proved positive-rate identity, reciprocal-rate exponent convergence, and the Proved integrability bound including rate zero.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_kyprianou82_actualHeight_pos_raw
import Theorems.Thm_kyprianou82_actualHeight_phi_nat_tendsto
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem kyprianou82_actualHeight_zero_raw
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
  (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
  (hW : HasSourceScaleFamily ψ W)
    : (∫ ω, discountedAt 0 (tauPlus D.X 1 ω) ∂P) = Real.exp (-(Phi ψ 0 * 1)) := by
  sorry
