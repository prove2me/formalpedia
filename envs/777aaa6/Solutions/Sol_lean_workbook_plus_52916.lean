-- Prove2me | solution 1 for lean_workbook_plus_52916
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:55:56.801974+00:00
-- url     : https://prove2.me/submissions/017e3850-2ba2-4b4b-9585-72590ca1e269

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≠ b) (hbc : b ≠ c)
    (hca : a ≠ c) :
    6 * a * b * c < a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) ∧
      a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) < 2 * (a ^ 3 + b ^ 3 + c ^ 3) := by
  have h1 : 0 < (a - b) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr hab)
  have h2 : 0 < (b - c) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr hbc)
  have h3 : 0 < (a - c) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr hca)
  constructor
  · nlinarith [mul_pos ha h2, mul_pos hb h3, mul_pos hc h1]
  · nlinarith [mul_pos (add_pos ha hb) h1, mul_pos (add_pos hb hc) h2, mul_pos (add_pos ha hc) h3]
