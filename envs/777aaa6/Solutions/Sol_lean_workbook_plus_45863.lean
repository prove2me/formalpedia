-- Prove2me | solution 1 for lean_workbook_plus_45863
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:28.363149+00:00
-- url     : https://prove2.me/submissions/9084bf92-d6c7-4bc4-91fb-3d03aab8f190

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h2 : a^2 + b^2 + c^2 = 1) (hn : n ≥ 2) : (a / (1 - a^n) + b / (1 - b^n) + c / (1 - c^n)) ≥ ((n + 1)^(1 + 1 / n)) / n := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
