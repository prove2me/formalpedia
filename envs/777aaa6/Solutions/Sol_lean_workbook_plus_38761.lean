-- Prove2me | solution 1 for lean_workbook_plus_38761
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:04.692246+00:00
-- url     : https://prove2.me/submissions/115d3f52-f46f-4362-a26e-9899a98053b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^2 * (x - 4)^3 * (x - 2) - 3 * x * (x - 4)^2 * (x - 2)^2 = x * (x - 4)^2 * (x - 2) * (x * (x - 4) - 3 * (x - 2)) := by
  (intros; linarith)
