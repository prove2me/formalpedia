-- Prove2me | solution 1 for lean_workbook_plus_13556
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:46:47.712201+00:00
-- url     : https://prove2.me/submissions/c4f4be27-f25c-4219-8bff-5c367238fcfe

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a^3 * b + b^3 * c + c^3 * a + a * b^3 + b * c^3 + c * a^3 := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (add_nonneg (sq_nonneg a) (sq_nonneg b)),
             mul_nonneg (sq_nonneg (b - c)) (add_nonneg (sq_nonneg b) (sq_nonneg c)),
             mul_nonneg (sq_nonneg (c - a)) (add_nonneg (sq_nonneg c) (sq_nonneg a))]
