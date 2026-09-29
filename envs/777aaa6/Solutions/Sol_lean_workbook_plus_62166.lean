-- Prove2me | solution 1 for lean_workbook_plus_62166
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:12.532715+00:00
-- url     : https://prove2.me/submissions/ec8c9b31-34c5-4d3e-89a3-d948c5b5f6d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x^2 + x*y + y^2)^2 / (x^2 + 2*x*y + 2*y^2) * (y^2 + 2*x*y + 2*x^2) = (x^2 + x*y + y^2)^2 / (x^2 + 2*x*y + 2*y^2) * (y^2 + 2*x*y + 2*x^2) := by
  norm_num
