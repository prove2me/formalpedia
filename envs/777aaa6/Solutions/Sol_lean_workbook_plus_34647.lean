-- Prove2me | solution 1 for lean_workbook_plus_34647
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:01.350849+00:00
-- url     : https://prove2.me/submissions/6beff53e-7cc8-43c8-b3dd-71cb3063e6c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : 4*x - 17*y = 1) : x = (1 + 17*y)/4 := by
  (intros; linarith)
