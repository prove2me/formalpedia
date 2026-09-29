-- Prove2me | solution 1 for lean_workbook_plus_75695
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:28.594019+00:00
-- url     : https://prove2.me/submissions/cec16083-b47b-4527-b3b5-f6aeb6596c06

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℝ → ℝ, ∀ x ∈ Set.Icc 0 1, (x ∈ Set.Icc 0 1 ∩ Set.range ((↑) : ℚ → ℝ)) → f x = 0 ∧ (x ∈ Set.Icc 0 1 \ Set.range ((↑) : ℚ → ℝ)) → f x = 1 := by
  (intros; simp_all)
