-- Prove2me | solution 1 for lean_workbook_plus_11629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:32.070487+00:00
-- url     : https://prove2.me/submissions/0a3cfbb0-7de3-45e0-a05a-1b536fa69cb5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (a^2 * b + b^2 * c + c^2 * a - 3 * a * b * c)^2 ≥ 0 := by
  (intros; positivity)
