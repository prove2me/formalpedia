-- Prove2me | solution 1 for lean_workbook_plus_21537
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:24:38.624707+00:00
-- url     : https://prove2.me/submissions/5537ece2-4d34-4b25-8f44-1e302d0fa86e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 >= (a^2 + b^2 + c^2) * a * b * c := by
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hbc.le) (sq_nonneg c)) (sq_nonneg (a - b)),
             mul_nonneg (mul_nonneg (sub_nonneg.2 hca.le) (sq_nonneg a)) (sq_nonneg (b - c)),
             mul_nonneg (mul_nonneg (sub_nonneg.2 hab.le) (sq_nonneg b)) (sq_nonneg (c - a))]
