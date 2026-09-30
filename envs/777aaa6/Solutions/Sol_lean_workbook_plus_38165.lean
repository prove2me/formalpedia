-- Prove2me | solution 1 for lean_workbook_plus_38165
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:57.066088+00:00
-- url     : https://prove2.me/submissions/5355d8ef-b9b9-425a-a8d2-99cc61c7b198

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 ≥ 1 / 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (add_nonneg (sq_nonneg (a + b)) (add_nonneg (sq_nonneg a) (sq_nonneg b))),
    mul_nonneg (sq_nonneg (b - c)) (add_nonneg (sq_nonneg (b + c)) (add_nonneg (sq_nonneg b) (sq_nonneg c))),
    mul_nonneg (sq_nonneg (c - a)) (add_nonneg (sq_nonneg (c + a)) (add_nonneg (sq_nonneg c) (sq_nonneg a)))]
