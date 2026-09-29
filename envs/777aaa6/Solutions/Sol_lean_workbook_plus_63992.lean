-- Prove2me | solution 1 for lean_workbook_plus_63992
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:32.617277+00:00
-- url     : https://prove2.me/submissions/461c029e-dca9-4e90-8897-54f8a9e6df2a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 0) : x^2 - 2*x + 2 - 9/(2*x) + 1/(81*x^2) = x^2 - 2*x + 2 - 9/(2*x) + 1/(81*x^2) := by
  norm_num
