-- Prove2me | solution 1 for lean_workbook_plus_4048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:44.595918+00:00
-- url     : https://prove2.me/submissions/a678513c-44cf-46f9-947e-2dab9ed5de0c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (2 * a ^ 2 - c ^ 2) ^ 2 + (2 * b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  (intros; positivity)
