-- Prove2me | solution 1 for lean_workbook_plus_15122
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:30:59.961172+00:00
-- url     : https://prove2.me/submissions/886bb0b3-94ac-4bc0-8871-6eb99bb1ea95

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (3 * a + 2 * b + c) + 1 / (3 * b + 2 * c + a) + 1 / (3 * c + 2 * a + b) ≤ 1 / 2 := by
  have hx : 0 < 3 * a + 2 * b + c := by positivity
  have hy : 0 < 3 * b + 2 * c + a := by positivity
  have hz : 0 < 3 * c + 2 * a + b := by positivity
  -- the key polynomial inequality, valid for all positive a, b, c
  have key : 0 ≤ 6 * (a ^ 3 + b ^ 3 + c ^ 3) + 25 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)
      + 23 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) - 18 * (a * b * c)
      - 22 * (a ^ 2 + b ^ 2 + c ^ 2) - 50 * (a * b + b * c + c * a) + 72 := by
    nlinarith [mul_nonneg ha.le (sq_nonneg (6 * (a - 1) + 5 * (b - 1) + 4 * (c - 1))),
      mul_nonneg ha.le (sq_nonneg (65 * (b - 1) - 38 * (c - 1))),
      mul_nonneg ha.le (sq_nonneg (c - 1)),
      mul_nonneg hb.le (sq_nonneg (6 * (b - 1) + 5 * (c - 1) + 4 * (a - 1))),
      mul_nonneg hb.le (sq_nonneg (65 * (c - 1) - 38 * (a - 1))),
      mul_nonneg hb.le (sq_nonneg (a - 1)),
      mul_nonneg hc.le (sq_nonneg (6 * (c - 1) + 5 * (a - 1) + 4 * (b - 1))),
      mul_nonneg hc.le (sq_nonneg (65 * (a - 1) - 38 * (b - 1))),
      mul_nonneg hc.le (sq_nonneg (b - 1)),
      sq_nonneg (a + b + c - 3)]
  rw [div_add_div _ _ hx.ne' hy.ne', div_add_div _ _ (by positivity) hz.ne',
    div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [key, habc]
