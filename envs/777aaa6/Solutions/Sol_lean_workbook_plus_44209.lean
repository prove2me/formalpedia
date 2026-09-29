-- Prove2me | solution 1 for lean_workbook_plus_44209
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:27.907664+00:00
-- url     : https://prove2.me/submissions/121d9492-0f08-40af-9c4e-b2d2d2def059

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c * d = 1) (h : a^2 + b^2 + c^2 + d^2 = 1) : a^2 / (a^2 + b * c) + b^2 / (b^2 + c * d) + c^2 / (c^2 + d * a) + d^2 / (d^2 + a * b) ≥ 1 + 16 * a * b * c * d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
