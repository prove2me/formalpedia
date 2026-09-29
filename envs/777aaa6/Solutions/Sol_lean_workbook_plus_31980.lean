-- Prove2me | solution 1 for lean_workbook_plus_31980
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:43.281819+00:00
-- url     : https://prove2.me/submissions/ab25cb16-1fdb-47aa-ad30-b58910475bd3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b) ^ 2 * (b + c) ^ 2 ≥ 4 * b * (a + c) * (b ^ 2 + a * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
