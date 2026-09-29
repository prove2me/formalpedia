-- Prove2me | solution 1 for lean_workbook_plus_8373
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:15.898105+00:00
-- url     : https://prove2.me/submissions/0edd8c1d-422a-4478-a64d-c89f4f8b404d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) : (x 1 - 1 / 2 * x 5) ^ 2 + (x 2 - 1 / 2 * x 5) ^ 2 + (x 3 - 1 / 2 * x 5) ^ 2 + (x 4 - 1 / 2 * x 5) ^ 2 ≥ 0 := by
  (intros; positivity)
