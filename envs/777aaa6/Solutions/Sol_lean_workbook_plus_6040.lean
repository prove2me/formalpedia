-- Prove2me | solution 1 for lean_workbook_plus_6040
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:00.139186+00:00
-- url     : https://prove2.me/submissions/71f69fbd-7e83-4950-8919-66a3b9f1b9f6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ x y z : ℝ, (4 * (y^2 * z^2 * x^2 * (x + y + z)^2 * (x^2 - x * y - x * z + y^2 - y * z + z^2)^2) / ((2 * x^2 + y * z)^2 * (z * x + 2 * y^2)^2 * (x * y + 2 * z^2)^2)) ≥ 0 := by
  (intros; positivity)
