-- Prove2me | solution 1 for lean_workbook_plus_32611
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:32.811747+00:00
-- url     : https://prove2.me/submissions/cea91794-a7c5-426f-a0ef-d84c8e275042

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 * (x - y) * (x - z) + y ^ 2 * (y - z) * (y - x) + z ^ 2 * (z - x) * (z - y) = 1 / 2 * ((y + z - x) ^ 2 * (y - z) ^ 2 + (z + x - y) ^ 2 * (z - x) ^ 2 + (x + y - z) ^ 2 * (x - y) ^ 2) := by
  (intros; linarith)
