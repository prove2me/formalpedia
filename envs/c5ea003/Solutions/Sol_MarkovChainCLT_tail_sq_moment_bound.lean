-- Prove2me | solution 1 for MarkovChainCLT.tail_sq_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T01:02:02.475524+00:00
-- url     : https://prove2.me/submissions/d2a7608a-54db-46f9-9e7b-10b80a143c1e

import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (δ M : ℝ) (hδ : 0 < δ) (hM : 0 < M)
    (hYm : Measurable Y)
    (hmom : Integrable (fun ω => |Y ω| ^ (2 + δ)) P) :
    ∫ ω, (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω ∂P
      ≤ (∫ ω, |Y ω| ^ (2 + δ) ∂P) / M ^ δ := by
  have hMδ : (0:ℝ) < M ^ δ := Real.rpow_pos_of_pos hM δ
  -- pointwise: Y²·1_{|Y|>M} ≤ |Y|^{2+δ} / M^δ
  have hpt : ∀ ω : Ω, (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω
      ≤ |Y ω| ^ (2 + δ) / M ^ δ := by
    intro ω
    by_cases h : M < |Y ω|
    · have hmem : ω ∈ {ω | M < |Y ω|} := h
      rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      have hpos : (0:ℝ) < |Y ω| := lt_trans hM h
      have hle : M ^ δ ≤ |Y ω| ^ δ :=
        Real.rpow_le_rpow (le_of_lt hM) h.le hδ.le
      have hnn2 : (0:ℝ) ≤ |Y ω| ^ (2:ℝ) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [← sq_abs, ← Real.rpow_two, le_div_iff₀ hMδ, Real.rpow_add hpos _ _]
      exact mul_le_mul_of_nonneg_left hle hnn2
    · have hmem : ω ∉ {ω | M < |Y ω|} := h
      rw [Set.indicator_of_notMem hmem, mul_zero]
      positivity
  -- integrate: RHS const-multiple integrable; LHS via mono
  have hR_int : Integrable (fun ω => |Y ω| ^ (2 + δ) / M ^ δ) P :=
    hmom.div_const _
  have hYabs : Measurable (fun ω => |Y ω|) :=
    (continuous_abs.measurable).comp hYm
  have hsetM : MeasurableSet {ω | M < |Y ω|} :=
    measurableSet_lt measurable_const hYabs
  have hL_meas : AEStronglyMeasurable
      (fun ω => (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω) P := by
    apply AEStronglyMeasurable.mul
    · exact (Measurable.pow_const hYm 2).aestronglyMeasurable
    · exact ((measurable_const).indicator hsetM).aestronglyMeasurable
  have hL_nn : ∀ ω : Ω, 0 ≤ (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω := by
    intro ω
    exact mul_nonneg (sq_nonneg _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hL_int : Integrable
      (fun ω => (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω) P :=
    hR_int.mono' hL_meas (by
      filter_upwards with ω
      rw [Real.norm_of_nonneg (hL_nn ω)]
      exact hpt ω)
  calc ∫ ω, (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω ∂P
      ≤ ∫ ω, |Y ω| ^ (2 + δ) / M ^ δ ∂P :=
        integral_mono_ae hL_int hR_int (by filter_upwards with ω using hpt ω)
    _ = (∫ ω, |Y ω| ^ (2 + δ) ∂P) / M ^ δ := integral_div _ _
