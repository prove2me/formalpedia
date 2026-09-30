-- Prove2me | solution 1 for lean_workbook_plus_55945
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:28.549525+00:00
-- url     : https://prove2.me/submissions/fcfa9fef-119d-479c-986e-afe559ae1ca4

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 3 / (a + 3) + 2 / (b + 2) + 1 / (c + 1) = 9 / 4 → 1 / a + 1 / b + 1 / c ≥ 1 := by
  intro _
  have hpa : 1 / a > 0 := by positivity
  have hpb : 1 / b > 0 := by positivity
  have hpc : 1 / c > 0 := by positivity
  rcases le_or_gt a 1 with h1 | h1
  · have : 1 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
    linarith
  rcases le_or_gt b 1 with h2 | h2
  · have : 1 ≤ 1 / b := by rw [le_div_iff₀ hb]; linarith
    linarith
  have h3 : c ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_lt_mul'' h1 h2 zero_le_one zero_le_one, mul_pos ha hb]
  have : 1 ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
  linarith
