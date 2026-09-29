-- Prove2me | solution 1 for lean_workbook_plus_70008
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:53:03.410864+00:00
-- url     : https://prove2.me/submissions/48887bfa-70d8-479c-a64f-414871d19ce9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^3 - 3*x + 2 ≥ 0 ↔ (x + 2)*(x - 1)^2 ≥ 0 := by
  (intros; ring)
