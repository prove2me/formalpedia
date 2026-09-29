-- Prove2me | solution 2 for MarkovChainCLT.tendstoInDistribution_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T08:41:23.913694+00:00
-- url     : https://prove2.me/submissions/d8dca1de-992d-4166-b412-19e9cacf0749

import Theorems.Thm_MarkovChainCLT_clt_iff_uniformlyIntegrable_of_alpha_mixing
import Theorems.Thm_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment
import Theorems.Thm_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum
import Theorems.Thm_MarkovChainCLT_tendstoInDistribution_inv_sqrt_of_normalized
import Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const
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
  set sig : ℝ := seqAsymptoticVariance P Y with hsig
  set v : ℕ → ℝ := fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P with hv
  -- Step 0: the log-moment hypothesis puts `Y 0` in `L²`.
  have hL2 : MemLp (Y 0) 2 P :=
    (MarkovChainCLT.memLp_two_and_logMoment_sub_const P (Y 0) (hY 0) hmom 0).1
  -- Step 1: the strong mixing coefficients tend to `0`, being squeezed by `c aⁿ`.
  have hα_nonneg : ∀ n : ℕ, 0 ≤ alphaMixingCoef P Y n := by
    intro n
    refine le_csSup ⟨1, ?_⟩
      ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
        @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
    rintro r ⟨k, A, B, -, -, rfl⟩
    have hAB1 : (P (A ∩ B)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ (A ∩ B)))
    have hA1 : (P A).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ A))
    have hB1 : (P B).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ B))
    have hA0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
    have hB0 : (0 : ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
    have hAB0 : (0 : ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> nlinarith
  have hα0 : Tendsto (fun n => alphaMixingCoef P Y n) atTop (𝓝 0) := by
    have hgeo : Tendsto (fun n : ℕ => c * a ^ n) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
      simpa using this.const_mul c
    exact squeeze_zero hα_nonneg hα hgeo
  -- Step 2: the variance of the partial sums grows linearly with slope `σ² > 0`.
  have hC1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * v n) atTop (𝓝 sig) :=
    MarkovChainCLT.tendsto_inv_mul_integral_sq_partialSum P Y hY hstat hL2 hsum
  have hvtop : Tendsto v atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * (sig / 2)) atTop atTop :=
      hn.atTop_mul_const (by positivity)
    refine tendsto_atTop_mono' atTop ?_ hlin
    have hev : ∀ᶠ n : ℕ in atTop, sig / 2 < (n : ℝ)⁻¹ * v n :=
      hC1.eventually (eventually_gt_nhds (by linarith))
    filter_upwards [hev, eventually_gt_atTop 0] with n hn1 hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have : (n : ℝ) * (sig / 2) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * v n) :=
      mul_le_mul_of_nonneg_left hn1.le hnpos.le
    calc (n : ℝ) * (sig / 2) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * v n) := this
      _ = v n := by field_simp
  -- Step 3: the CLT for the self-normalized sums, from Theorem 3 and uniform integrability.
  have hUI := MarkovChainCLT.uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment
    P Y hY hstat hcent c a ha0 ha1 hα hmom hsum hvar
  have hnorm := (MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing P Y hY hstat hcent
    hL2 hα0 hvtop).2 hUI
  -- Step 4: change the normalisation from `σ_n` to `√n`.
  have hs : 0 < Real.sqrt sig := Real.sqrt_pos.2 hvar
  have hd : Tendsto (fun n : ℕ => Real.sqrt (v n) / Real.sqrt n) atTop (𝓝 (Real.sqrt sig)) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ)⁻¹ * v n)) atTop (𝓝 (Real.sqrt sig)) :=
      (Real.continuous_sqrt.tendsto sig).comp hC1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0, hvtop.eventually_ge_atTop 0] with n hn0 hvn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
    ring
  have hXmeas : ∀ n : ℕ, Measurable fun ω => ∑ i ∈ Finset.range n, Y i ω :=
    fun n => Finset.measurable_sum _ fun i _ => hY i
  have hfin := MarkovChainCLT.tendstoInDistribution_inv_sqrt_of_normalized P
    (fun n ω => ∑ i ∈ Finset.range n, Y i ω) (fun n => Real.sqrt (v n)) (Real.sqrt sig) hs
    hXmeas hd hnorm
  have hsq : Real.toNNReal (Real.sqrt sig ^ 2) = sig.toNNReal := by
    rw [Real.sq_sqrt hvar.le]
  rwa [hsq] at hfin
