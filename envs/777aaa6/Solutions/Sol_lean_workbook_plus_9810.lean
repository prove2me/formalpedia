-- Prove2me | solution 1 for lean_workbook_plus_9810
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:25.480905+00:00
-- url     : https://prove2.me/submissions/76f4a55e-9871-4c0b-a512-2e25f8a8c9cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 - 2 * y ^ 2 * z ^ 2 - 2 * z ^ 2 * x ^ 2 - 2 * x ^ 2 * y ^ 2 = -(x + y + z) * (y + z - x) * (z + x - y) * (x + y - z) := by
  (intros; linarith)
