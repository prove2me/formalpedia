-- Prove2me | solution 1 for lean_workbook_plus_15499
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:17.884692+00:00
-- url     : https://prove2.me/submissions/d1f5797f-6ed7-42bf-b427-ba6c16c2dd17

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) :
  (a * b * Real.sqrt (2 - 2 * c)) / (a + b) + (b * c * Real.sqrt (2 - 2 * a)) / (b + c) + (c * a * Real.sqrt (2 - 2 * b)) / (c + a) ≤ 3 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
