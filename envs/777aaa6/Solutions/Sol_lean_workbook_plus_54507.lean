-- Prove2me | solution 1 for lean_workbook_plus_54507
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:08.002736+00:00
-- url     : https://prove2.me/submissions/b08dcba5-165f-44a2-b806-ecaf2058f93d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 8*x*(x*y - 2) + 48*(x*y - 2) = 8*(x + 6)*(x*y - 2) := by
  (intros; linarith)
