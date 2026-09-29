-- Prove2me | solution 1 for lean_workbook_plus_30596
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:00.306597+00:00
-- url     : https://prove2.me/submissions/fa9e7820-b78a-4e96-bc0c-f08e90da52f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (1 / 3) * ((4 * a - 5 * b + 4 * c) ^ 2 * (4 * a + 4 * b - 5 * c) ^ 2) ≥ 0 := by
  (intros; positivity)
