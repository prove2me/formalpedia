-- Prove2me | solution 1 for lean_workbook_plus_48595
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:40.681712+00:00
-- url     : https://prove2.me/submissions/a1e59788-2d05-448d-8baa-808cbfc83758

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : 3*x + 4*y = 4) (h₂ : 2*x + 6*y = 9) : 10*x + 20*y = 26 := by
  (intros; linarith)
