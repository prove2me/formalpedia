-- Prove2me | solution 1 for lean_workbook_plus_55146
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:31.161316+00:00
-- url     : https://prove2.me/submissions/ea53b42b-c0e8-4a65-8ae0-3fdae429ee88

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 →
  x^2*y^2*z + y*z^2*x^2 + y^2*z^2*x + y^5 - z^2*x^3 + x^5 - y^3*z^2 - x^3*y^2 - x^2*y^3 - z^3*x^2 - z^3*y^2 + z^5 =
  (x - y)^2 * (x - z)^2 * x + 3 * (x - y)^2 * (x + y - z)^2 * (y / 3 + z / 3) + 3 * (x - z)^2 * (x - y + z)^2 * (y / 3 + z / 3) + (y - z)^2 * y * z * (y + z) := by
  (intros; linarith)
