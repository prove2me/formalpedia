-- Prove2me | solution 1 for lean_workbook_plus_57390
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:27.677075+00:00
-- url     : https://prove2.me/submissions/f299c7ad-e593-475c-b498-b6610928b51e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^2 / (1 + b * c) + b^2 / (1 + c * a) + c^2 / (1 + a * b) ≤ 3 / (4 * (a * b + b * c + c * a)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
