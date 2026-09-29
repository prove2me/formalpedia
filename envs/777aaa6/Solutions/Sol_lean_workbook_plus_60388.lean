-- Prove2me | solution 1 for lean_workbook_plus_60388
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:10.797882+00:00
-- url     : https://prove2.me/submissions/d5be6fa1-7039-4335-a48d-da112c312662

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 25 * (9 * x ^ 2 + 16 * y ^ 2) ≥ (9 * x + 16 * y) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
