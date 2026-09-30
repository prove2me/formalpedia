-- Prove2me | solution 2 for lean_workbook_plus_73424
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:50.702146+00:00
-- url     : https://prove2.me/submissions/bc4d1c57-6d85-4cf6-a791-749ed8a4a044

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
