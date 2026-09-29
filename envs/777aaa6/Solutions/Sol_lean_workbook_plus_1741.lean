-- Prove2me | solution 1 for lean_workbook_plus_1741
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:45.881707+00:00
-- url     : https://prove2.me/submissions/84ad000b-6f6e-4f46-a391-66baa4b864e1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
