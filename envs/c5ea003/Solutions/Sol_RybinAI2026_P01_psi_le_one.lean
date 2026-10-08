-- Prove2me | solution 1 for RybinAI2026.P01.psi_le_one
-- status  : ACCEPTED   (disprove)
-- author  : @moona3k
-- created : 2026-10-06T13:46:37.776981+00:00
-- url     : https://prove2.me/submissions/ed2a2b59-3998-4c01-9dbe-d01cd65ef8cd

import Mathlib

open MeasureTheory

/-- `psi_le_one` is false: for `t = 1/2` the integrand `(1 - s²/2)⁻¹` is at least `1 + s²/2`
on `[0,1]`, so the integral is at least `7/6 > 1`. -/
theorem solution : ¬ (∀ {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1),
    (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) ≤ 1) := by
  intro h
  have h0 := h (t := 1 / 2) (by norm_num) (by norm_num)
  have hcont1 : Continuous (fun s : ℝ => 1 + s ^ 2 / 2) := by fun_prop
  have hpos : ∀ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → 0 < 1 + (1 / 2 - 1) * s ^ 2 := by
    intro s hs
    have : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    linarith
  have hle : ∀ s ∈ Set.Icc (0:ℝ) 1, 1 + s ^ 2 / 2 ≤ (1 + (1 / 2 - 1) * s ^ 2)⁻¹ := by
    intro s hs
    have hp := hpos s hs
    rw [le_inv_comm₀ (by positivity) hp, inv_eq_one_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]
  have hint2 : IntervalIntegrable (fun s : ℝ => (1 + (1 / 2 - 1) * s ^ 2)⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs; exact (hpos s hs).ne'
  have hmono := intervalIntegral.integral_mono_on zero_le_one (hcont1.intervalIntegrable 0 1) hint2 hle
  have hval : ∫ s in (0:ℝ)..1, (1 + s ^ 2 / 2) = 7 / 6 := by
    simp [integral_pow]
    norm_num
  linarith
