-- Prove2me | solution 1 for MarkovChainCLT.tendstoInDistribution_of_bounded_of_summable_alpha
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T10:57:55.804567+00:00
-- url     : https://prove2.me/submissions/27b94ffb-37a7-4596-8152-0f2a0717426e

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov
import Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_bounded
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by
  have hL2 : MemLp (Y 0) 2 P := by
    have hsq_meas : Measurable (fun ω => (Y 0 ω) ^ 2) := by
      simpa [pow_two] using (hY 0).mul (hY 0)
    have hInt : Integrable (fun ω => (Y 0 ω) ^ 2) P := by
      refine Integrable.mono' (g := fun _ => B ^ 2) (integrable_const _)
        hsq_meas.aestronglyMeasurable ?_
      filter_upwards [hB 0] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hB0 : 0 ≤ B
      · exact le_of_lt (sq_lt_sq' (abs_lt.mp hω).1 (abs_lt.mp hω).2)
      · have hBneg : B < 0 := lt_of_not_ge hB0
        have hcon : (0 : ℝ) ≤ |Y 0 ω| := abs_nonneg _
        linarith
    exact (memLp_two_iff_integrable_sq (hY 0).aestronglyMeasurable).mpr hInt
  have hlim :=
    var_partialSum_div_tendsto_of_summable_cov P Y hY hstat hcent hL2 hsum
  exact clt_of_var_limit_of_bounded P Y hY hstat hcent B hB hα hlim hvar
