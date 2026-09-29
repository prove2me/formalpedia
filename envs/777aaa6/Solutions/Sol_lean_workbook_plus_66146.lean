-- Prove2me | solution 1 for lean_workbook_plus_66146
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:50.256419+00:00
-- url     : https://prove2.me/submissions/c67245dd-0eb7-49d7-a407-b62cbbf6f86c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha1 : 1 ≥ a) (ha2 : a ≥ 1/3) : 4 * a ^ 3 + 2 * a ^ 2 + 13 * a - 1 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a)])
