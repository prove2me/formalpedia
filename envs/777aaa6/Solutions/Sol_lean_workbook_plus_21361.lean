-- Prove2me | solution 1 for lean_workbook_plus_21361
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:10.58066+00:00
-- url     : https://prove2.me/submissions/d44d3e60-4ac3-4ed1-89f8-d043d315dc88

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a ^ 3 * (b + c) + b ^ 3 * (a + c) + c ^ 3 * (a + b) = 0) : a * b + b * c + c * a ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
