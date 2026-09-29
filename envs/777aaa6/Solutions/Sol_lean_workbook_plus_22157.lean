-- Prove2me | solution 1 for lean_workbook_plus_22157
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:12.351875+00:00
-- url     : https://prove2.me/submissions/95791400-59a8-4e95-8fd3-6b82382c880c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℂ) :
  x^3 + y^3 + z^3 - 3 * x * y * z
  = (x + y + z) * (x^2 + y^2 + z^2 - x * y - x * z - y * z) := by
  (intros; ring)
