-- Prove2me | solution 1 for lean_workbook_plus_67999
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:20.851936+00:00
-- url     : https://prove2.me/submissions/be3f638f-af33-4a1b-a421-044fc7e9ca9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
    (x * y^2 + y * z^2 + x^2 * z) * (x^2 * y + y^2 * z + z^2 * x) - (x * y + x * z + y * z) * (x^2 * y^2 + y^2 * z^2 + x^2 * z^2) = x * y * z * (x * (x - y) * (x - z) + y * (y - x) * (y - z) + z * (z - x) * (z - y)) := by
  (intros; linarith)
