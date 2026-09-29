-- Prove2me | solution 1 for lean_workbook_plus_68311
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:41.997024+00:00
-- url     : https://prove2.me/submissions/f77b2924-b083-46d5-a4ed-44f9283e7570

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 5 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * (x * y + y * z + z * x) = (2 * x - y) ^ 2 + (2 * y - z) ^ 2 + (2 * z - x) ^ 2 := by
  (intros; linarith)
