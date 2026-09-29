-- Prove2me | solution 1 for lean_workbook_plus_53463
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:25.851632+00:00
-- url     : https://prove2.me/submissions/b481081f-9e72-4c92-aabe-2d68f29db2db

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (x^2 + y^2 + z^2 = 3 ∧ (x + y)^2 + (y + z)^2 + (x + z)^2 ≤ 12 → x*y + y*z + z*x ≤ 3) := by
  (intros; linarith)
