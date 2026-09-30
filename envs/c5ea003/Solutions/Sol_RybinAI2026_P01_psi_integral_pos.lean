-- Prove2me | solution 1 for RybinAI2026.P01.psi_integral_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:47:51.648289+00:00
-- url     : https://prove2.me/submissions/dcd3f061-1104-4e97-8c5a-12d49a5af2d8

import Mathlib

open MeasureTheory

theorem solution (t : ℝ) (ht : 0 < t) :
    0 < ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
  have hden : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + (t - 1) * s ^ 2 := by
    intro s hs
    by_cases h : t ≤ 1
    · have hsq : s ^ 2 ≤ 1 := by
        have hmul := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr h)
      nlinarith
    · have ht1 : 1 < t := lt_of_not_ge h
      nlinarith [sq_nonneg s]
  have hcont : ContinuousOn
      (fun s : ℝ => 1 + (t - 1) * s ^ 2) (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hk : ContinuousOn
      (fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹) (Set.uIcc (0 : ℝ) 1) :=
    hcont.inv₀ (by
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
        simpa only [Set.uIcc_of_le zero_le_one] using hs
      exact ne_of_gt (hden s hs'))
  have hfi : IntervalIntegrable
      (fun s : ℝ => (1 + (t - 1) * s ^ 2)⁻¹) volume 0 1 :=
    hk.intervalIntegrable
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hfi
  · intro s hs
    exact inv_pos.mpr (hden s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
  · exact zero_lt_one
