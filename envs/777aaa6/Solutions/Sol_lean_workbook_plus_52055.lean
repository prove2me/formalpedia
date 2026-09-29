-- Prove2me | solution 1 for lean_workbook_plus_52055
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:13.801744+00:00
-- url     : https://prove2.me/submissions/f715fd2a-5919-41e4-8099-7b3d6aae438c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (x + y + z) ^ 3 - 8 * (y ^ 2 * x + z ^ 2 * y + x ^ 2 * z) = x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y) + 4 * (x - y) * (x - z) * (y - z) + 3 * x * y * z := by
  (intros; linarith)
