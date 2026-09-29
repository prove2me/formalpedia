-- Prove2me | solution 1 for lean_workbook_plus_77634
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:19:33.893149+00:00
-- url     : https://prove2.me/submissions/15c550bf-9fd5-434e-a447-9a3d7a8f4ad7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : abs x ≥ x := by
  exact le_abs_self x
