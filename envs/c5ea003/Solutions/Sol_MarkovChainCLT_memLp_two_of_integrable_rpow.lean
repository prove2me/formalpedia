-- Prove2me | solution 1 for MarkovChainCLT.memLp_two_of_integrable_rpow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:41:56.189506+00:00
-- url     : https://prove2.me/submissions/091e2070-7f46-4986-a857-bed0b62ba4cb

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hYm : AEStronglyMeasurable Y P)
    (hmom : Integrable (fun ω => |Y ω| ^ (2 + δ)) P) :
    MemLp Y 2 P := by
  have h2δ_pos : (0 : ℝ) < 2 + δ := by linarith
  -- Step 1: MemLp Y (ofReal (2+δ)) from integrability
  have hMem_hi : MemLp Y (ENNReal.ofReal (2 + δ)) P := by
    constructor
    · exact hYm
    · -- eLpNorm finite from HasFiniteIntegral of |Y|^(2+δ)
      have hfi := hmom.hasFiniteIntegral
      -- HasFiniteIntegral means ∫⁻ ‖·‖ₑ < ∞ for the integrand
      rw [HasFiniteIntegral] at hfi
      -- relate ∫⁻ ‖|Y|^...‖ₑ to ∫⁻ ‖Y‖ₑ^(2+δ)
      have heq : (∫⁻ ω, ‖(fun ω => |Y ω| ^ (2 + δ)) ω‖ₑ ∂P)
          = ∫⁻ ω, ‖Y ω‖ₑ ^ (2 + δ) ∂P := by
        apply lintegral_congr_ae
        filter_upwards with ω
        have h1 : ‖(fun ω => |Y ω| ^ (2 + δ)) ω‖ₑ
            = ENNReal.ofReal (|Y ω| ^ (2 + δ)) := by
          rw [Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ |Y ω| ^ (2 + δ))]
        have h2 : ENNReal.ofReal (|Y ω| ^ (2 + δ))
            = ‖Y ω‖ₑ ^ (2 + δ) := by
          simp only [Real.enorm_eq_ofReal_abs]
          exact (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) h2δ_pos.le).symm
        rw [h1, h2]
      rw [heq] at hfi
      -- eLpNorm Y (ofReal (2+δ)) = (∫⁻ ‖Y‖ₑ^(2+δ))^(1/(2+δ)) < ∞
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ne_of_gt (ENNReal.ofReal_pos.mpr h2δ_pos)) ENNReal.ofReal_ne_top]
      rw [ENNReal.toReal_ofReal h2δ_pos.le]
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfi.ne
  -- Step 2: mono down to 2 (finite measure, 2 ≤ ofReal (2+δ))
  apply hMem_hi.mono_exponent
  have h2eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
    norm_num [ENNReal.ofReal_ofNat]
  rw [h2eq]
  exact ENNReal.ofReal_le_ofReal (by linarith)
