-- Prove2me | solution 1 for posted_price_revenue_tendsto_zero_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T01:40:19.49089+00:00
-- url     : https://prove2.me/submissions/a88870c1-e4a7-4548-94ab-a65cf96148d3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : Integrable (fun v : ℝ => v) ν) :
    Tendsto (fun p : ℝ => p * (ν (Ici p)).toReal) atTop (nhds 0) := by
  have habs : Integrable (fun v : ℝ => |v|) ν := hint.abs
  -- Step 1: the tail integrals ∫_{[p,∞)} |v| dν tend to 0 by dominated convergence.
  have hI : Tendsto (fun p : ℝ => ∫ v, (Ici p).indicator (fun w => |w|) v ∂ν) atTop
      (nhds (∫ _v, (0 : ℝ) ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun v : ℝ => |v|)
    · exact Filter.Eventually.of_forall fun p =>
        habs.aestronglyMeasurable.indicator measurableSet_Ici
    · refine Filter.Eventually.of_forall fun p => ae_of_all ν fun v => ?_
      by_cases hv : v ∈ Ici p
      · simp [Set.indicator_of_mem hv, Real.norm_eq_abs, abs_abs]
      · simp [Set.indicator_of_notMem hv, abs_nonneg]
    · exact habs
    · refine ae_of_all ν fun v => ?_
      have hev : (fun p : ℝ => (Ici p).indicator (fun w => |w|) v) =ᶠ[atTop]
          fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_atTop v] with p hp
        exact Set.indicator_of_notMem (by simp only [Set.mem_Ici, not_le]; exact hp) _
      exact tendsto_const_nhds.congr' hev.symm
  rw [integral_zero] at hI
  -- Step 2: Markov bound p * ν([p,∞)) ≤ ∫_{[p,∞)} |v| dν for p ≥ 0.
  have key : ∀ p : ℝ, 0 ≤ p →
      p * (ν (Ici p)).toReal ≤ ∫ v, (Ici p).indicator (fun w => |w|) v ∂ν := by
    intro p hp
    rw [integral_indicator measurableSet_Ici]
    have h1 : p * (ν (Ici p)).toReal = ∫ _ in Ici p, p ∂ν := by
      rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
    rw [h1]
    refine setIntegral_mono_on (integrableOn_const (measure_ne_top ν _))
      habs.integrableOn measurableSet_Ici fun x hx => ?_
    exact le_trans (Set.mem_Ici.mp hx) (le_abs_self x)
  -- Step 3: squeeze.
  have hge : ∀ᶠ p : ℝ in atTop, 0 ≤ p * (ν (Ici p)).toReal := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with p hp
    exact mul_nonneg hp ENNReal.toReal_nonneg
  have hle : ∀ᶠ p : ℝ in atTop,
      p * (ν (Ici p)).toReal ≤ ∫ v, (Ici p).indicator (fun w => |w|) v ∂ν := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with p hp using key p hp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hI hge hle
