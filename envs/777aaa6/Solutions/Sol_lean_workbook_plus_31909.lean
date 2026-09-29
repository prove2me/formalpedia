-- Prove2me | solution 1 for lean_workbook_plus_31909
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:35.252469+00:00
-- url     : https://prove2.me/submissions/a98b015f-67ec-4b80-a84b-637994d384fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx: (x - 1) * (x - 3) ≤ 0) : 1 ≤ x ∧ x ≤ 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
