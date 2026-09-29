-- Prove2me | solution 1 for lean_workbook_plus_10912
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:26.739738+00:00
-- url     : https://prove2.me/submissions/f7ff33a8-949f-4330-8140-f41e1c637f3c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y : ℤ} (h : x^2 - 2*y^2 = -2) : (3*x + 4*y)^2 - 2*(2*x + 3*y)^2 = -2 := by
  (intros; linarith)
