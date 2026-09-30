-- Prove2me | solution 1 for lean_workbook_plus_33542
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:55.225877+00:00
-- url     : https://prove2.me/submissions/b660db66-a098-4c29-b13e-1b8c36fe34a3

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^3 + b^2 + c ≥ a^4 + b^3 + c^3) : a^3 + b^3 + 2*c^3 ≤ 4 := by
  have h1 : 0 ≤ (a - 1)^2 * (3 * a^2 + 2 * a + 1) := mul_nonneg (sq_nonneg _) (by positivity)
  have h2 : 0 ≤ (b - 1)^2 * (2 * b + 1) := mul_nonneg (sq_nonneg _) (by positivity)
  have h3 : 0 ≤ (c - 1)^2 * (c + 2) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith [h1, h2, h3]
