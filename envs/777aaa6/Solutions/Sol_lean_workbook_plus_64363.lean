-- Prove2me | solution 1 for lean_workbook_plus_64363
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:46.074044+00:00
-- url     : https://prove2.me/submissions/1a5e63ea-8c37-4be3-a5c0-4eb326da9bde

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (a + c) * (b + c) ≥ (8:ℝ) / 9 * (a + b + c) * (a * b + a * c + b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
