-- Prove2me | solution 1 for BanditAlgorithm.le_cam_cauchy_affinity
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T23:38:18.506294+00:00
-- url     : https://prove2.me/submissions/27523b15-bdec-4ead-a6ac-080e58affdce

import Mathlib

open MeasureTheory InformationTheory
open scoped ENNReal

theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ ω, (P.rnDeriv (P + Q) ω * Q.rnDeriv (P + Q) ω) ^ (2⁻¹ : ℝ)
          ∂(P + Q)) ^ 2 ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  set ν : Measure Ω := P + Q with hν
  set p : Ω → ℝ≥0∞ := P.rnDeriv ν with hp
  set q : Ω → ℝ≥0∞ := Q.rnDeriv ν with hq
  have hpm : Measurable p := Measure.measurable_rnDeriv P ν
  have hqm : Measurable q := Measure.measurable_rnDeriv Q ν
  -- Both densities integrate to `1` against `ν = P + Q`.
  have hPν : P ≪ ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hQν : Q ≪ ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hip : ∫⁻ ω, p ω ∂ν = 1 := by rw [hp, Measure.lintegral_rnDeriv hPν, measure_univ]
  have hiq : ∫⁻ ω, q ω ∂ν = 1 := by rw [hq, Measure.lintegral_rnDeriv hQν, measure_univ]
  -- The pointwise maximum integrates to at most `2`.
  have hmax : ∫⁻ ω, max (p ω) (q ω) ∂ν ≤ 2 := by
    calc ∫⁻ ω, max (p ω) (q ω) ∂ν
        ≤ ∫⁻ ω, p ω + q ω ∂ν :=
          lintegral_mono fun ω => max_le_add_of_nonneg bot_le bot_le
      _ = 2 := by rw [lintegral_add_left hpm, hip, hiq]; norm_num
  -- Cauchy–Schwarz applied to `√min · √max = √(pq)`.
  have hsq : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x := by
    intro x; rw [← ENNReal.rpow_mul]; norm_num
  have hsq' : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ 2 = x := by
    intro x; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hfg : ∀ ω, (min (p ω) (q ω)) ^ (2⁻¹ : ℝ) * (max (p ω) (q ω)) ^ (2⁻¹ : ℝ) =
      (p ω * q ω) ^ (2⁻¹ : ℝ) := by
    intro ω
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), min_mul_max]
  have hCS : ∫⁻ ω, (p ω * q ω) ^ (2⁻¹ : ℝ) ∂ν ≤
      (∫⁻ ω, min (p ω) (q ω) ∂ν) ^ (2⁻¹ : ℝ) * (∫⁻ ω, max (p ω) (q ω) ∂ν) ^ (2⁻¹ : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
      (f := fun ω => (min (p ω) (q ω)) ^ (2⁻¹ : ℝ))
      (g := fun ω => (max (p ω) (q ω)) ^ (2⁻¹ : ℝ))
      ((hpm.min hqm).pow_const _).aemeasurable ((hpm.max hqm).pow_const _).aemeasurable
    simp only [Pi.mul_apply, hfg, hsq, one_div] at h
    exact h
  calc (2 : ℝ≥0∞)⁻¹ * (∫⁻ ω, (p ω * q ω) ^ (2⁻¹ : ℝ) ∂ν) ^ 2
      ≤ (2 : ℝ≥0∞)⁻¹ * ((∫⁻ ω, min (p ω) (q ω) ∂ν) ^ (2⁻¹ : ℝ) *
          (∫⁻ ω, max (p ω) (q ω) ∂ν) ^ (2⁻¹ : ℝ)) ^ 2 := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ * ((∫⁻ ω, min (p ω) (q ω) ∂ν) * ∫⁻ ω, max (p ω) (q ω) ∂ν) := by
          rw [mul_pow, hsq', hsq']
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((∫⁻ ω, min (p ω) (q ω) ∂ν) * 2) := by gcongr
    _ = ∫⁻ ω, min (p ω) (q ω) ∂ν := by
          rw [mul_comm _ (2 : ℝ≥0∞), ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
