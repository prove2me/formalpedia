-- Prove2me | solution 1 for MarkovChainCLT.tendstoInDistribution_gaussian_of_L1_approx
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:16:24.847403+00:00
-- url     : https://prove2.me/submissions/c914c461-52bc-46d8-bc83-e007886022de

import Theorems.Thm_ProbabilityTheory_tendsto_integral_gaussianReal_of_tendsto
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (W : ℕ → ℕ → Ω → ℝ) (v : ℕ → ℝ≥0) (c : ℝ≥0) (δ : ℕ → ℝ)
    (hY : ∀ n, Measurable (Y n))
    (hW : ∀ K, TendstoInDistribution (W K) atTop (id : ℝ → ℝ) (fun _ => μ)
      (gaussianReal 0 (v K)))
    (hint : ∀ K n, Integrable (fun ω => |Y n ω - W K n ω|) μ)
    (hδ : ∀ K n, ∫ ω, |Y n ω - W K n ω| ∂μ ≤ δ K)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hv : Tendsto (fun K => (v K : ℝ)) atTop (𝓝 (c : ℝ))) :
    TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 c) := by
  classical
  refine ⟨fun n => (hY n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  have hfcont : Continuous f := hL.continuous
  have hfb : ∀ x, |f x| ≤ |f 0| + C := by
    intro x
    have h1 := hC x 0
    rw [Real.dist_eq] at h1
    have h2 : |f x| - |f 0| ≤ |f x - f 0| := abs_sub_abs_le_abs_sub _ _
    linarith
  -- integrability of `f` composed with any almost-everywhere measurable random variable
  have hfint : ∀ (V : Ω → ℝ), AEMeasurable V μ → Integrable (fun ω => f (V ω)) μ := by
    intro V hV
    exact ⟨(hfcont.measurable.comp_aemeasurable hV).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := |f 0| + C)
        (ae_of_all _ (fun ω => by simpa using hfb (V ω)))⟩
  -- rewrite the two sides as integrals over `Ω` and over `ℝ`
  simp only [ProbabilityMeasure.coe_mk]
  have hmapY : ∀ n : ℕ, ∫ x, f x ∂(μ.map (Y n)) = ∫ ω, f (Y n ω) ∂μ := fun n => by
    rw [integral_map (hY n).aemeasurable hfcont.aestronglyMeasurable]
  have hmapl : ∫ x, f x ∂((gaussianReal 0 c).map (id : ℝ → ℝ)) = ∫ x, f x ∂(gaussianReal 0 c) := by
    rw [integral_map measurable_id.aemeasurable hfcont.aestronglyMeasurable]
    rfl
  simp only [hmapY, hmapl]
  -- the approximating sequences converge to their own Gaussians
  have hWlim : ∀ K, Tendsto (fun n => ∫ ω, f (W K n ω) ∂μ) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 (v K)))) := by
    intro K
    have h := tendsto_iff_forall_lipschitz_integral_tendsto.mp (hW K).tendsto f ⟨C, hC⟩ ⟨L, hL⟩
    simp only [ProbabilityMeasure.coe_mk] at h
    have hmapW : ∀ n : ℕ, ∫ x, f x ∂(μ.map (W K n)) = ∫ ω, f (W K n ω) ∂μ := fun n => by
      rw [integral_map ((hW K).forall_aemeasurable n) hfcont.aestronglyMeasurable]
    have hmapl' : ∫ x, f x ∂((gaussianReal 0 (v K)).map (id : ℝ → ℝ))
        = ∫ x, f x ∂(gaussianReal 0 (v K)) := by
      rw [integral_map measurable_id.aemeasurable hfcont.aestronglyMeasurable]
      rfl
    simp only [hmapW, hmapl'] at h
    exact h
  -- the Gaussians converge as the variances do
  have hGlim : Tendsto (fun K => ∫ x, f x ∂(gaussianReal 0 (v K))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 c))) :=
    ProbabilityTheory.tendsto_integral_gaussianReal_of_tendsto v c hv f L hL C hC
  -- the uniform-in-`n` approximation error
  have hδnn : ∀ K, 0 ≤ δ K := by
    intro K
    exact le_trans (integral_nonneg (fun ω => abs_nonneg _)) (hδ K 0)
  have happ : ∀ K n, |(∫ ω, f (Y n ω) ∂μ) - ∫ ω, f (W K n ω) ∂μ| ≤ (L : ℝ) * δ K := by
    intro K n
    have hiY : Integrable (fun ω => f (Y n ω)) μ := hfint _ (hY n).aemeasurable
    have hiW : Integrable (fun ω => f (W K n ω)) μ := hfint _ ((hW K).forall_aemeasurable n)
    have hsub : (∫ ω, f (Y n ω) ∂μ) - ∫ ω, f (W K n ω) ∂μ
        = ∫ ω, (f (Y n ω) - f (W K n ω)) ∂μ := (integral_sub hiY hiW).symm
    rw [hsub]
    have hptw : ∀ ω, |f (Y n ω) - f (W K n ω)| ≤ (L : ℝ) * |Y n ω - W K n ω| := by
      intro ω
      have h := hL.dist_le_mul (Y n ω) (W K n ω)
      rwa [Real.dist_eq, Real.dist_eq] at h
    calc |∫ ω, (f (Y n ω) - f (W K n ω)) ∂μ|
        ≤ ∫ ω, |f (Y n ω) - f (W K n ω)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (L : ℝ) * |Y n ω - W K n ω| ∂μ :=
          integral_mono (hiY.sub hiW).abs ((hint K n).const_mul _) hptw
      _ = (L : ℝ) * ∫ ω, |Y n ω - W K n ω| ∂μ := integral_const_mul _ _
      _ ≤ (L : ℝ) * δ K :=
          mul_le_mul_of_nonneg_left (hδ K n) (NNReal.coe_nonneg L)
  -- the three-epsilon argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hLpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  obtain ⟨K1, hK1⟩ := (Metric.tendsto_atTop.mp hGlim) (ε / 3) (by linarith)
  obtain ⟨K2, hK2⟩ := (Metric.tendsto_atTop.mp hδ0) (ε / (3 * ((L : ℝ) + 1))) (by positivity)
  set K : ℕ := max K1 K2 with hK
  have hg1 : |(∫ x, f x ∂(gaussianReal 0 (v K))) - ∫ x, f x ∂(gaussianReal 0 c)| < ε / 3 := by
    have := hK1 K (le_max_left _ _)
    rwa [Real.dist_eq] at this
  have hg2 : (L : ℝ) * δ K < ε / 3 := by
    have h := hK2 K (le_max_right _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδnn K)] at h
    have h2 : (L : ℝ) * δ K ≤ ((L : ℝ) + 1) * δ K :=
      mul_le_mul_of_nonneg_right (by linarith) (hδnn K)
    have h3 : ((L : ℝ) + 1) * δ K < ((L : ℝ) + 1) * (ε / (3 * ((L : ℝ) + 1))) :=
      mul_lt_mul_of_pos_left h hLpos
    have h4 : ((L : ℝ) + 1) * (ε / (3 * ((L : ℝ) + 1))) = ε / 3 := by
      field_simp
    linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hWlim K)) (ε / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hg3 : |(∫ ω, f (W K n ω) ∂μ) - ∫ x, f x ∂(gaussianReal 0 (v K))| < ε / 3 := by
    have := hN n hn
    rwa [Real.dist_eq] at this
  have hg4 := happ K n
  calc |(∫ ω, f (Y n ω) ∂μ) - ∫ x, f x ∂(gaussianReal 0 c)|
      ≤ |(∫ ω, f (Y n ω) ∂μ) - ∫ ω, f (W K n ω) ∂μ|
        + |(∫ ω, f (W K n ω) ∂μ) - ∫ x, f x ∂(gaussianReal 0 (v K))|
        + |(∫ x, f x ∂(gaussianReal 0 (v K))) - ∫ x, f x ∂(gaussianReal 0 c)| := by
        have e1 := abs_sub_le (∫ ω, f (Y n ω) ∂μ) (∫ ω, f (W K n ω) ∂μ)
          (∫ x, f x ∂(gaussianReal 0 (v K)))
        have e2 := abs_sub_le (∫ ω, f (Y n ω) ∂μ) (∫ x, f x ∂(gaussianReal 0 (v K)))
          (∫ x, f x ∂(gaussianReal 0 c))
        linarith
    _ < ε := by linarith
