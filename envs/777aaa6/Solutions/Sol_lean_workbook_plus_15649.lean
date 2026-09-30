-- Prove2me | solution 1 for lean_workbook_plus_15649
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:43.992228+00:00
-- url     : https://prove2.me/submissions/b1fd8a5f-114f-4fe3-8920-c4e7ec9293b1

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : x ≠ 0) : (x ^ 12 - x ^ 9 - x ^ 3 + 1) / x ^ 4 ≥ 0 := by
  apply div_nonneg
  · have e : x ^ 12 - x ^ 9 - x ^ 3 + 1 = (x ^ 3 - 1) ^ 2 * (x ^ 6 + x ^ 3 + 1) := by ring
    rw [e]
    apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg (x ^ 3 + 1 / 2)]
  · positivity
