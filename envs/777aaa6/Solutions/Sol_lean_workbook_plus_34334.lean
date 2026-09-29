-- Prove2me | solution 1 for lean_workbook_plus_34334
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:46.098548+00:00
-- url     : https://prove2.me/submissions/50fc2639-f514-4a99-b126-72a1b88e380c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℝ, (Real.sqrt a - 1 / 2)^2 + (Real.sqrt b - 1 / 2)^2 ≥ 0 := by
  (intros; positivity)
