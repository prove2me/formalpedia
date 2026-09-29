-- Prove2me | solution 1 for lean_workbook_plus_36865
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:12.40703+00:00
-- url     : https://prove2.me/submissions/9fb9690e-7cbb-4917-943e-f5975e860b6c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (h₁ : a 1 = 1 / 2) (h₂ : a 2 = 1 / 2) (h₃ : a 3 = 1 / 2) (h₄ : a 4 = 1 / 2) : a 1 = a 2 ∧ a 2 = a 3 ∧ a 3 = a 4 ∧ a 4 = 1 / 2 := by
  (intros; simp_all)
