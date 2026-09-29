-- Prove2me | solution 1 for lean_workbook_plus_72723
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:00.141434+00:00
-- url     : https://prove2.me/submissions/cc0667c0-48d5-4983-9afb-d37e78f09a2d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x ^ 2 * y + x ^ 2 * z + y ^ 2 * x + y ^ 2 * z + z ^ 2 * x + z ^ 2 * y) + 6 * x * y * z := by
  (intros; linarith)
