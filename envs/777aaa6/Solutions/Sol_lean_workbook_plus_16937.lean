-- Prove2me | solution 1 for lean_workbook_plus_16937
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:37.599859+00:00
-- url     : https://prove2.me/submissions/fc68838c-92a5-48ec-95dd-150aa966c88a

import Mathlib
set_option autoImplicit false

theorem solution :
  IsGreatest {y : ℝ | ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ y = 2 * x * (1 - x)^2} (8 / 27)   := by
  constructor
  refine' ⟨1 / 3, by norm_num, by norm_num, by ring⟩
  norm_num
  norm_num
  ring
  intro y hy
  obtain ⟨x, hx0, hx1, rfl⟩ := hy
  have : 0 ≤ (x - 1 / 3)^2 := sq_nonneg (x - 1 / 3)
  nlinarith

#print axioms solution
