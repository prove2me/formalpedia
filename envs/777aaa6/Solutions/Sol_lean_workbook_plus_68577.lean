-- Prove2me | solution 1 for lean_workbook_plus_68577
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:32.038715+00:00
-- url     : https://prove2.me/submissions/f72e272d-e0ca-4de1-8b55-c35805e50ebb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a + b + c) + 3 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
