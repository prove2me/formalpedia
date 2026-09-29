-- Prove2me | solution 1 for lean_workbook_plus_51440
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:43.166071+00:00
-- url     : https://prove2.me/submissions/f2e809de-ea5f-43f1-a993-4842c7b7454c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 * (y - z) ^ 2 + y ^ 4 * (z - x) ^ 2 + z ^ 4 * (x - y) ^ 2 ≥ 0 := by
  (intros; positivity)
