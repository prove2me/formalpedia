-- Prove2me | solution 1 for lean_workbook_plus_24325
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:29.095616+00:00
-- url     : https://prove2.me/submissions/6247ddd3-8dcc-4dd6-ae90-d31db36264fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (habc : a + b + c = 1) : (a + b) * (b + c) * (c + a) = a + b + c - 1 → a * b * c ≤ (5 * Real.sqrt 5 - 9) / 54 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
