-- Prove2me | solution 1 for lean_workbook_plus_20808
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:58.492274+00:00
-- url     : https://prove2.me/submissions/ae4afb7b-ec4d-4417-9c2f-46efcf5cbd1d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * b * (b + c) ^ 2 + b * c * (a + b) ^ 2 ≤ (a + b) ^ 2 * (b + c) ^ 2 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
