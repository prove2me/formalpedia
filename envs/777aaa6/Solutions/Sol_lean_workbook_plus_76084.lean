-- Prove2me | solution 1 for lean_workbook_plus_76084
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:44.511959+00:00
-- url     : https://prove2.me/submissions/7a5add9d-95e5-4e30-8863-675f3e5ca395

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : 3 * Real.sqrt (a * b * c) * (a + b + c) ≤ 8 + a * b * c := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ a * b * c by positivity), Real.sqrt_nonneg (a * b * c), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
