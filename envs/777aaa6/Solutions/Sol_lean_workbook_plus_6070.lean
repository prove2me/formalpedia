-- Prove2me | solution 1 for lean_workbook_plus_6070
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:55.202712+00:00
-- url     : https://prove2.me/submissions/eb94f2de-ab8d-4d2f-a1e8-20b9dd76d1bc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (x ^ 5 + y ^ 5 + z ^ 5) = 3 * (x + y + z) ^ 5 + 5 * (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) * (x ^ 3 + y ^ 3 + z ^ 3 - (x + y + z) ^ 3) := by
  (intros; linarith)
