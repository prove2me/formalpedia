-- Prove2me | solution 1 for lean_workbook_plus_23447
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:28.258843+00:00
-- url     : https://prove2.me/submissions/70f3267e-a849-497c-9afd-cec39a5d1b20

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 7 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + 27 ≥ 17 * (a + b + c) := by
  nlinarith [mul_nonneg hb (sq_nonneg (a - 1)), mul_nonneg hc (sq_nonneg (b - 1)),
    mul_nonneg ha (sq_nonneg (c - 1)), sq_nonneg (a + b + c - 3),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
