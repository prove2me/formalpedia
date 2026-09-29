-- Prove2me | solution 1 for MarkovChainCLT.tendstoInDistribution_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T08:39:07.006817+00:00
-- url     : https://prove2.me/submissions/35cc93b5-53d4-401d-8001-dd191718c938

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov
import Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_exp_alpha
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by
  have hL2 : MemLp (Y 0) 2 P := by
    have hsq_meas : Measurable (fun ω => (Y 0 ω) ^ 2) := by
      simpa [pow_two] using (hY 0).mul (hY 0)
    have hdom : Integrable
        (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω| + Real.exp 1 ^ 2) P :=
      hmom.add (integrable_const _)
    have hbound : ∀ᵐ ω ∂P, ‖(Y 0 ω) ^ 2‖
        ≤ (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω| + Real.exp 1 ^ 2 := by
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hle : Real.exp 1 ≤ |Y 0 ω|
      · have he1 : (1 : ℝ) ≤ Real.exp 1 := by
          have h := Real.add_one_le_exp (1 : ℝ)
          linarith
        have hpos : (0 : ℝ) < |Y 0 ω| :=
          lt_of_lt_of_le (Real.exp_pos 1) hle
        have hlog : (1 : ℝ) ≤ Real.log |Y 0 ω| :=
          (Real.le_log_iff_exp_le hpos).mpr hle
        have hpl : (1 : ℝ) ≤ Real.posLog |Y 0 ω| := by
          rw [Real.posLog_eq_log (by rw [abs_abs]; exact le_trans he1 hle)]
          exact hlog
        have hstep : (Y 0 ω) ^ 2 ≤ (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω| :=
          le_mul_of_one_le_right (sq_nonneg _) hpl
        have he2 : (0 : ℝ) ≤ (Real.exp 1) ^ 2 := sq_nonneg _
        calc (Y 0 ω) ^ 2 ≤ (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω| := hstep
          _ ≤ _ + Real.exp 1 ^ 2 := by linarith
      · have habs : |Y 0 ω| < Real.exp 1 := lt_of_not_ge hle
        have hmem := abs_lt.mp habs
        have h1 : (Y 0 ω) ^ 2 < (Real.exp 1) ^ 2 :=
          sq_lt_sq' hmem.1 hmem.2
        have hnn : (0 : ℝ) ≤ (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω| :=
          mul_nonneg (sq_nonneg _) Real.posLog_nonneg
        linarith
    have hInt : Integrable (fun ω => (Y 0 ω) ^ 2) P :=
      hdom.mono' hsq_meas.aestronglyMeasurable hbound
    exact (memLp_two_iff_integrable_sq (hY 0).aestronglyMeasurable).mpr hInt
  have hlim :=
    var_partialSum_div_tendsto_of_summable_cov P Y hY hstat hcent hL2 hsum
  exact clt_of_var_limit_of_exp_alpha P Y hY hstat hcent c a ha0 ha1 hα hmom hlim hvar
