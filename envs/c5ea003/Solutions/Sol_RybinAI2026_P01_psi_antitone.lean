-- Prove2me | solution 1 for RybinAI2026.P01.psi_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:19:22.566358+00:00
-- url     : https://prove2.me/submissions/24763be0-c44e-40b6-94ac-4ff9b7fef015

import Mathlib

open MeasureTheory

theorem solution (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (∫ x in (0 : ℝ)..1, (1 + (t - 1) * x ^ 2)⁻¹) ≤
      ∫ x in (0 : ℝ)..1, (1 + (s - 1) * x ^ 2)⁻¹ := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hden_pos (q : ℝ) (hq : 0 < q) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      0 < 1 + (q - 1) * x ^ 2 := by
    by_cases hq1 : q ≤ 1
    · have hx2 : x ^ 2 ≤ 1 := by
        have hmul := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hx2 (sub_nonneg.mpr hq1)
      nlinarith
    · have hq1' : 1 < q := lt_of_not_ge hq1
      nlinarith [sq_nonneg x]
  have hden_cont (q : ℝ) : ContinuousOn
      (fun x : ℝ => 1 + (q - 1) * x ^ 2) (Set.uIcc 0 1) := by fun_prop
  have hinv_cont (q : ℝ) (hq : 0 < q) : ContinuousOn
      (fun x : ℝ => (1 + (q - 1) * x ^ 2)⁻¹) (Set.uIcc 0 1) := by
    apply (hden_cont q).inv₀
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hx
    exact ne_of_gt (hden_pos q hq x hx')
  have hint : IntervalIntegrable (fun x : ℝ => (1 + (t - 1) * x ^ 2)⁻¹) volume 0 1 :=
    (hinv_cont t ht).intervalIntegrable
  have hins : IntervalIntegrable (fun x : ℝ => (1 + (s - 1) * x ^ 2)⁻¹) volume 0 1 :=
    (hinv_cont s hs).intervalIntegrable
  apply intervalIntegral.integral_mono_on zero_le_one hint hins
  intro x hx
  have hdt := hden_pos t ht x hx
  have hds := hden_pos s hs x hx
  have hden : 1 + (s - 1) * x ^ 2 ≤ 1 + (t - 1) * x ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_right hst 1) (sq_nonneg x)
    nlinarith
  exact (inv_le_inv₀ hdt hds).2 hden
