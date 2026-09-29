-- Prove2me | solution 1 for lean_workbook_plus_34004
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:53.725719+00:00
-- url     : https://prove2.me/submissions/610e6db6-78ec-4818-9ee4-046fbec787c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h : a ≥ 1) : a ^ 3 + 3 * a ^ 2 - 4 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a)])
