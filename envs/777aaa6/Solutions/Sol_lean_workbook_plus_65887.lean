-- Prove2me | solution 1 for lean_workbook_plus_65887
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:10.213281+00:00
-- url     : https://prove2.me/submissions/db071cff-7fe3-453c-8246-b2295f662a18

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  (x + 1) ^ 2 / 4 ≤ 1 := by
  (intros; nlinarith [sq_nonneg (x)])
