-- Prove2me | solution 1 for lean_workbook_plus_6148
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:23.557318+00:00
-- url     : https://prove2.me/submissions/c898893d-6da5-4136-ac9a-e919028a6138

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℚ, x^2 + x - 1 ≠ 0 → ∃ y : ℚ, x = (y^3 + 2*y^2 - (y^2 + y)) / (y^2 + y - 1) := by
  intro x hx
  refine ⟨x, ?_⟩
  rw [eq_div_iff hx]
  ring
