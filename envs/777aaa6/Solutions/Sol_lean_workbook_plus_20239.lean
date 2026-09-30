-- Prove2me | solution 1 for lean_workbook_plus_20239
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:08.884463+00:00
-- url     : https://prove2.me/submissions/663e4e1b-4600-45bd-be57-edf9ef3ae3c1

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / a + 1 / b + 1 / c ≥ 25 / (1 + 48 * a * b * c) := by
  have h48 : 1 + 48 * a * b * c = 49 := by linear_combination 48 * habc
  rw [h48]
  have h1 : 0 < 1 / a := by positivity
  have h2 : 0 < 1 / b := by positivity
  have h3 : 0 < 1 / c := by positivity
  have key : 1 ≤ 1 / a ∨ 1 ≤ 1 / b ∨ 1 ≤ 1 / c := by
    rcases le_or_gt a 1 with h | h
    · left; rw [le_div_iff₀ ha]; linarith
    · rcases le_or_gt b 1 with h' | h'
      · right; left; rw [le_div_iff₀ hb]; linarith
      · right; right
        have hab : 1 < a * b := by nlinarith
        have hc1 : c < 1 := by
          by_contra hcon
          push_neg at hcon
          nlinarith
        rw [le_div_iff₀ hc]; linarith
  have h25 : (25 : ℝ) / 49 < 1 := by norm_num
  rcases key with k | k | k <;> linarith
