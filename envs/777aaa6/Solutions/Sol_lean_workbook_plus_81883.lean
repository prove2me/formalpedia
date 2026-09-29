-- Prove2me | solution 1 for lean_workbook_plus_81883
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:03.642075+00:00
-- url     : https://prove2.me/submissions/54d1199b-7cf7-48da-86b5-6cdcb9d2652d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^3 + y^3 + z^3 - 3 * x * y * z = 1 / 2 * (x + y + z) * ( (x - y)^2 + (y - z)^2 + (z - x)^2) := by
  (intros; linarith)
