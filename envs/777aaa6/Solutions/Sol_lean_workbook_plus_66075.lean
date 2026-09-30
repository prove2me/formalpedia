-- Prove2me | solution 1 for lean_workbook_plus_66075
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:27.718846+00:00
-- url     : https://prove2.me/submissions/d221ff40-7bc3-4f9e-b7fa-972cac1c6c1d

import Mathlib
set_option autoImplicit false

theorem solution : ∀ y : ℝ, (y ≤ -1 ∨ 0 ≤ y ∧ y ≤ 1) ↔ 2*y - 2*y^3 ≥ 0   := by
  intro y
  constructor
  · rintro (hleft | ⟨hzero, hone⟩)
    · have hp : 0 ≤ (2 * (-y)) * (1 - y) * (-1 - y) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith only [hp]
    · have hp : 0 ≤ (2 * y) * (1 - y) * (1 + y) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith only [hp]
  · intro h
    by_cases hleft : y ≤ -1
    · exact Or.inl hleft
    · have hgt : -1 < y := lt_of_not_ge hleft
      have hzero : 0 ≤ y := by
        by_contra hnegative
        have hy : y < 0 := lt_of_not_ge hnegative
        have hp : 0 < (2 * (-y)) * (1 - y) * (1 + y) :=
          mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
        nlinarith only [hp, h]
      have hone : y ≤ 1 := by
        by_contra hlarge
        have hy : 1 < y := lt_of_not_ge hlarge
        have hp : 0 < (2 * y) * (y - 1) * (1 + y) :=
          mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
        nlinarith only [hp, h]
      exact Or.inr ⟨hzero, hone⟩

#print axioms solution
