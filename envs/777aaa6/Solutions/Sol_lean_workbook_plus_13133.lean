-- Prove2me | solution 1 for lean_workbook_plus_13133
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:50.975262+00:00
-- url     : https://prove2.me/submissions/737ce732-3011-47e3-ab60-b4aa3bd40b7d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) := by
  (intros; linarith)
