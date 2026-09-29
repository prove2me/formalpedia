-- Prove2me | solution 1 for lean_workbook_plus_67663
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:42.745027+00:00
-- url     : https://prove2.me/submissions/f2bbbc98-b26c-4b88-a092-6e62d9911c44

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :  (a^2 + b^2 + c^2) * (1 / a^2 + 1 / b^2 + 1 / c^2) ≥ 3 + (2 * (a^3 + b^3 + c^3)) / (a * b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
