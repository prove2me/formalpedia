-- Prove2me | solution 1 for lean_workbook_plus_31804
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:41.835715+00:00
-- url     : https://prove2.me/submissions/87556f01-75d0-4797-a50d-f5a5a8299998

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ x y z : ℝ, x^3 + y^3 + z^3 - (x + y + z) * (x * y + x * z + y * z) + 6 * x * y * z = (x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y)) := by
  (intros; linarith)
