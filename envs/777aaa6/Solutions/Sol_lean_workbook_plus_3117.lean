-- Prove2me | solution 1 for lean_workbook_plus_3117
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:25.528407+00:00
-- url     : https://prove2.me/submissions/5ed5cf2d-a1ba-410a-98af-2b6f193d85f3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) (k_1 k_2 : ℤ) : (x^2 + y - (k_1^2)) - (y^2 + x - k_2^2) = (x - y) * (x + y - 1) - (k_1 - k_2) * (k_1 + k_2) := by
  (intros; linarith)
