-- Prove2me | solution 1 for lean_workbook_plus_10262
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:43.063188+00:00
-- url     : https://prove2.me/submissions/97040507-ecbd-48dc-b72e-a712fb129043

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : (x ^ 2 * (2 * y - 1) ^ 2 + y ^ 2 * (2 * z - 1) ^ 2 + z ^ 2 * (2 * x - 1) ^ 2) + 5 - (1 + x) * (1 + y) * (1 + z) - 3 * (1 - x) * (1 - y) * (1 - z) = (2 * x * y - x - 1) ^ 2 + (2 * y * z - y - 1) ^ 2 + (2 * z * x - z - 1) ^ 2 := by
  (intros; linarith)
