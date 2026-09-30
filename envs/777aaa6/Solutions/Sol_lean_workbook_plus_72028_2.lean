-- Prove2me | solution 2 for lean_workbook_plus_72028
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:09.350949+00:00
-- url     : https://prove2.me/submissions/512c372a-05b5-41c4-8f56-7f9f16c214a0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1) (h : a * b + b * c + c * a = 4) : 5 * a + 4 * b + c ≤ 25 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
