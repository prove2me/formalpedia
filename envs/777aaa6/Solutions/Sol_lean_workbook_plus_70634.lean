-- Prove2me | solution 1 for lean_workbook_plus_70634
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:16.493778+00:00
-- url     : https://prove2.me/submissions/b3aff44b-3de0-44a5-b61e-dd9c509af3fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * b * c * (a + b + c) ≤ (1 / 3) * (a * b + b * c + c * a) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
