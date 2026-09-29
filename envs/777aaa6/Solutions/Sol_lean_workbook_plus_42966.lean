-- Prove2me | solution 1 for lean_workbook_plus_42966
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:38.884262+00:00
-- url     : https://prove2.me/submissions/b1995810-965e-4f11-87ea-5437a1b957ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a + b + c + Real.sqrt (a * b * c)) = 1 → (a + b + c) ^ 2 + 2 * Real.sqrt (a * b * c) * (a + b + c) ≥ 4 * (a * b + b * c + a * c) := by
  (intros; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ a * b * c by positivity), Real.sq_sqrt (show (0:ℝ) ≤ a * b * c by positivity), Real.sqrt_nonneg (a * b * c), Real.sqrt_nonneg (a * b * c), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
