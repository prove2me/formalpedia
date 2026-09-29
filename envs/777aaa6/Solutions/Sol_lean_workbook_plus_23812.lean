-- Prove2me | solution 1 for lean_workbook_plus_23812
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:30.998071+00:00
-- url     : https://prove2.me/submissions/406d41c5-8ec9-40fd-b898-a9149b105f8b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^3 / (2 * b + 3 * c) + b^3 / (2 * c + 3 * a) + c^3 / (2 * a + 3 * b) ≥ 1 / 5 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
