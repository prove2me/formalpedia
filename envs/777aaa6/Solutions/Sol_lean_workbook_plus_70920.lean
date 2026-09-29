-- Prove2me | solution 1 for lean_workbook_plus_70920
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:37.708092+00:00
-- url     : https://prove2.me/submissions/2ea79a0e-c7b0-4efb-b55e-2c4b7555ae53

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  6 * (3 * x * y + 4 * x * z + 2 * y * z) + 6 * x + 3 * y + 4 * z + 72 * x * y * z ≤ 12 * (x + 1 / 6) * (2 * y + 2 / 3) * (3 * z + 3 / 4) - 1 := by
  (intros; linarith)
