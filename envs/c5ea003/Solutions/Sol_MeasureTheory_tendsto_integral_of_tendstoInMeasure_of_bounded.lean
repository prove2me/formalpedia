-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_of_tendstoInMeasure_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:25:49.531274+00:00
-- url     : https://prove2.me/submissions/a44a166e-fa3b-42a5-bfb3-fdb9518cae23

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

/-- **Bounded convergence theorem in probability**. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℕ → Ω → ℝ) (hG : ∀ n, Measurable (G n)) (B : ℝ) (hB : ∀ n ω, |G n ω| ≤ B)
    (h0 : TendstoInMeasure μ G atTop 0) :
    Tendsto (fun n => ∫ ω, G n ω ∂μ) atTop (𝓝 0) := by
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : μ Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 hne.some)
  have hint : ∀ n, Integrable (G n) μ :=
    fun n => ⟨(hG n).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun ω => by
        simpa [Real.norm_eq_abs] using hB n ω))⟩
  -- the basic `δ`-splitting estimate
  have key : ∀ δ : ℝ, 0 < δ → ∀ n,
      |∫ ω, G n ω ∂μ| ≤ δ + B * (μ.real {ω | δ ≤ |G n ω|}) := by
    intro δ hδ n
    set S : Set Ω := {ω | δ ≤ |G n ω|} with hS
    have hSm : MeasurableSet S :=
      measurableSet_le measurable_const (continuous_abs.measurable.comp (hG n))
    have hpt : ∀ ω, |G n ω| ≤ δ + B * S.indicator (fun _ => (1:ℝ)) ω := by
      intro ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω]
        have h1 := hB n ω
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hω]
        simp only [hS, Set.mem_setOf_eq, not_le] at hω
        simp only [mul_zero, add_zero]
        linarith
    have hintR : Integrable (fun ω => δ + B * S.indicator (fun _ => (1:ℝ)) ω) μ := by
      refine (integrable_const δ).add (Integrable.const_mul ?_ B)
      exact (integrable_const (1:ℝ)).indicator hSm
    calc |∫ ω, G n ω ∂μ| ≤ ∫ ω, |G n ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (δ + B * S.indicator (fun _ => (1:ℝ)) ω) ∂μ :=
          integral_mono (hint n).abs hintR hpt
      _ = δ + B * (μ.real S) := by
          rw [integral_add (integrable_const δ)
            (Integrable.const_mul ((integrable_const (1:ℝ)).indicator hSm) B)]
          rw [integral_const, integral_const_mul, integral_indicator hSm]
          simp [Measure.real]
  -- convergence in measure, in real-valued form
  have hreal : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μ.real {ω | δ ≤ |G n ω|}) atTop (𝓝 0) := by
    intro δ hδ
    have := (tendstoInMeasure_iff_measureReal_norm (μ := μ) (f := G) (g := 0)).mp h0 δ hδ
    simpa [Real.norm_eq_abs] using this
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hpos : 0 < ε / (2 * (B + 1)) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hreal (ε/2) (by linarith)) _ hpos
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ μ.real _)] at h1
  have h2 : B * (μ.real {ω | ε/2 ≤ |G n ω|}) < ε / 2 := by
    have hb : B * (μ.real {ω | ε/2 ≤ |G n ω|}) ≤ (B + 1) * (μ.real {ω | ε/2 ≤ |G n ω|}) := by
      have : (0:ℝ) ≤ μ.real {ω | ε/2 ≤ |G n ω|} := by positivity
      nlinarith
    have hb2 : (B + 1) * (μ.real {ω | ε/2 ≤ |G n ω|}) < (B + 1) * (ε / (2 * (B + 1))) := by
      apply mul_lt_mul_of_pos_left h1 (by linarith)
    have : (B + 1) * (ε / (2 * (B + 1))) = ε / 2 := by
      field_simp
    linarith
  have h3 := key (ε/2) (by linarith) n
  rw [Real.dist_eq, sub_zero]
  linarith
