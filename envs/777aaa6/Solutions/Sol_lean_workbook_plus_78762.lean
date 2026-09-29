-- Prove2me | solution 1 for lean_workbook_plus_78762
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:49.755155+00:00
-- url     : https://prove2.me/submissions/6862a251-867a-4358-8076-2bdfe8309f6f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (1/2)*((a-b)^2 + (b-c)^2 + (c-a)^2) ≥ 0 := by
  (intros; positivity)
