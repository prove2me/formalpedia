-- Prove2me | solution 1 for lean_workbook_plus_69695
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:25.96495+00:00
-- url     : https://prove2.me/submissions/d21fb2dc-3b3a-452c-bfa9-6bf03cc23111

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (8 * a - 11 * b - 7 * c) ^ 2 + 23 * (b - 3 * c) ^ 2 ≥ 0 := by
  (intros; positivity)
