-- Prove2me | solution 1 for lean_workbook_plus_50857
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:43.198457+00:00
-- url     : https://prove2.me/submissions/1584c736-35d5-4cac-bbbd-7f4e1cb0d04e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
