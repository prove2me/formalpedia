-- Prove2me | solution 1 for lean_workbook_plus_60467
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:39.522996+00:00
-- url     : https://prove2.me/submissions/e01f9cc4-f6f9-409e-a33a-a991dfe057c4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0 := by
  (intros; positivity)
