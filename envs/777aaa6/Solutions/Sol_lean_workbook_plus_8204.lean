-- Prove2me | solution 1 for lean_workbook_plus_8204
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:28.9656+00:00
-- url     : https://prove2.me/submissions/926ca727-9706-4388-9997-c200240829cd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^3 + y^3 + z^3 = 3 * x * y * z + (x + y + z) * (x^2 + y^2 + z^2 - x * y - y * z - z * x) := by
  (intros; linarith)
