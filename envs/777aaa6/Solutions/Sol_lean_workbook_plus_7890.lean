-- Prove2me | solution 1 for lean_workbook_plus_7890
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:56:55.529632+00:00
-- url     : https://prove2.me/submissions/4709de1c-aeae-496e-bd34-388bbfee6e28

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 := by
  (intros; positivity)
