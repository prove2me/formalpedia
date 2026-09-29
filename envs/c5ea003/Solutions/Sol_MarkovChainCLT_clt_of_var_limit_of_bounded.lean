-- Prove2me | solution 1 for MarkovChainCLT.clt_of_var_limit_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T12:13:42.186968+00:00
-- url     : https://prove2.me/submissions/8829ad9f-f593-4e9c-bd19-5a9aae3860de

import Theorems.Thm_MarkovChainCLT_clt_iff_uniformlyIntegrable_of_alpha_mixing
import Theorems.Thm_MarkovChainCLT_uniformIntegrable_sq_partialSum_of_bounded_of_summable_alpha
import Theorems.Thm_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha
import Theorems.Thm_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum
import Theorems.Thm_MarkovChainCLT_tendstoInDistribution_inv_sqrt_of_normalized
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
    (hvarlim : Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by
  set sig : ℝ := seqAsymptoticVariance P Y with hsig
  set v : ℕ → ℝ := fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P with hv
  -- Step 0: a uniformly bounded variable on a probability space is square integrable.
  have hL2 : MemLp (Y 0) 2 P := by
    refine MemLp.of_bound (hY 0).aestronglyMeasurable B ?_
    filter_upwards [hB 0] with ω hω
    simpa [Real.norm_eq_abs] using hω.le
  -- Step 1: the positive-lag autocovariance series converges absolutely.
  have hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P :=
    MarkovChainCLT.summable_covariance_of_bounded_of_summable_alpha P Y hY hstat hcent B hB hα
  -- Step 2: the strong mixing coefficients tend to `0`, being the terms of a convergent series.
  have hα0 : Tendsto (fun n => alphaMixingCoef P Y n) atTop (𝓝 0) := hα.tendsto_atTop_zero
  -- Step 3: the variance of the partial sums grows linearly with slope `σ² > 0`.
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
    have hle : (n : ℝ) * (sig / 2) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * v n) :=
      mul_le_mul_of_nonneg_left hn1.le hnpos.le
    calc (n : ℝ) * (sig / 2) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * v n) := hle
      _ = v n := by field_simp
  -- Step 4: the CLT for the self-normalised sums, from Theorem 3 and uniform integrability.
  have hUI := MarkovChainCLT.uniformIntegrable_sq_partialSum_of_bounded_of_summable_alpha
    P Y hY hstat hcent B hB hα hvar
  have hnorm := (MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing P Y hY hstat hcent
    hL2 hα0 hvtop).2 hUI
  -- Step 5: change the normalisation from `σ_n` to `√n`.
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
