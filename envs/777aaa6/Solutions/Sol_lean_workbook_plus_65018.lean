-- Prove2me | solution 1 for lean_workbook_plus_65018
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:43.077184+00:00
-- url     : https://prove2.me/submissions/1fe3577a-8cc5-4245-a9cc-fd028a1de9e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 9 * (a^3 + 3 * b^3 + 5 * c^3) ≥ (a^2 + 3 * b^2 + 5 * c^2) * (a + 3 * b + 5 * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
