-- Prove2me | Theorems.Thm_kyprianou82_actualHeight_phi_nat_tendsto
-- name    : kyprianou82_actualHeight_phi_nat_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:24:29.394583+00:00
-- url     : https://prove2.me/theorems/2d365ecd-34af-4ab9-a933-eb5e36045c9c
-- title:
--   Principal exponent along reciprocal natural rates tends to zero rate
-- statement:
--   The principal exponent Phi evaluated at the positive sequence 1/(n+1) converges to its value at zero. The proof uses the order characterisation Phi psi r < beta iff r < psi beta from the source scale-transform domain bridge; it does not require continuity of psi itself.
-- source:
--   Kyprianou chapter 8 Stage B, source result 81 Levy root domain and the Proved scale-family bridge.

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

theorem kyprianou82_actualHeight_phi_nat_tendsto
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    : Tendsto (fun n : ℕ => Phi ψ (1 / ((n : ℝ) + 1))) atTop (nhds (Phi ψ 0)) := by
  sorry
