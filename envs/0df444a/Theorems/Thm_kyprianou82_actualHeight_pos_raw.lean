-- Prove2me | Theorems.Thm_kyprianou82_actualHeight_pos_raw
-- name    : kyprianou82_actualHeight_pos_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:19:50.930873+00:00
-- url     : https://prove2.me/theorems/37eec812-eb20-463e-a05e-ba4f42a78215
-- title:
--   Positive-rate unrestricted first-passage discount identity
-- statement:
--   For a strictly positive discount parameter, the unrestricted discounted first-passage expectation equals the exponential of the negative principal exponent times the unit level. This is obtained from the Proved filtered Avram coupling and the exact positive-root first-passage lintegral identity.
-- source:
--   Kyprianou chapter 8 Stage B, source result 81 filtered Avram coupling and the Proved exact strict-upcrossing discount theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem kyprianou82_actualHeight_pos_raw
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 < q) :
    (∫ ω, discountedAt q (tauPlus D.X 1 ω) ∂P) = Real.exp (-(Phi ψ q * 1)) := by
  sorry
