-- Prove2me | solution 1 for lean_workbook_plus_64830
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:18.712289+00:00
-- url     : https://prove2.me/submissions/2b293bfd-1f84-40ea-89a5-23bd5e2e0e78

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℂ) : x^4 + y^4 + z^4 - 2 * x^2 * y^2 - 2 * x^2 * z^2 - 2 * y^2 * z^2 = -(x + y + z) * (x + y - z) * (-x + y + z) * (x - y + z) := by
  (intros; ring)
