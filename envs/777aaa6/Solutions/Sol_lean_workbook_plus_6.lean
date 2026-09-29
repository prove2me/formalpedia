-- Prove2me | solution 1 for lean_workbook_plus_6
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:52.792486+00:00
-- url     : https://prove2.me/submissions/b9b7e218-89c1-4613-acca-8054ac996295

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℤ) :
  (x^2 + 1) * (y^2 + 1) * (z^2 + 1) =
  (x + y + z)^2 - 2 * (x * y + y * z + z * x) + (x * y + y * z + z * x)^2 - 2 * x * y * z * (x + y + z) + x^2 * y^2 * z^2 + 1 := by
  (intros; linarith)
