-- Prove2me | solution 1 for lean_workbook_plus_58507
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:00.748142+00:00
-- url     : https://prove2.me/submissions/0811e82e-d487-477f-9024-9d6aac837e50

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = (5/3 : ℝ)^(1/2) - 1) : (1/2)*x^3 = (1/2)*((5/3 : ℝ)^(1/2) - 1)^3 := by
  (intros; simp_all)
