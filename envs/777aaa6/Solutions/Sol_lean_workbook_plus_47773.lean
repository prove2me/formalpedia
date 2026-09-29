-- Prove2me | solution 1 for lean_workbook_plus_47773
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:57.531965+00:00
-- url     : https://prove2.me/submissions/c7a2d126-e0c1-4d4c-b888-a5717c55a600

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y + z) * (x + y - z) * (y + z - x) * (z + x - y) = 2 * x ^ 2 * y ^ 2 + 2 * y ^ 2 * z ^ 2 + 2 * z ^ 2 * x ^ 2 - x ^ 4 - y ^ 4 - z ^ 4 := by
  (intros; linarith)
