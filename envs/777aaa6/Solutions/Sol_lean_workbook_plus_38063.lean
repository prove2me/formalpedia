-- Prove2me | solution 1 for lean_workbook_plus_38063
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:54.856496+00:00
-- url     : https://prove2.me/submissions/62deaf47-ab25-47fc-9189-e1c88e08b4d3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h₁ : 3 * a ^ 2 - 12 * a ≤ 0) (h₂ : 0 ≤ a) (h₃ : a ≤ 4) : 0 ≤ a ∧ a ≤ 4 := by
  (intros; simp_all)
