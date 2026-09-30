-- Prove2me | solution 1 for lean_workbook_plus_47866
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:37.910375+00:00
-- url     : https://prove2.me/submissions/76748848-896a-4602-b49c-f8a2b2a50815

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y : ℝ, (x ≠ 0 ∧ y ≠ 0) → x / (x ^ 2 + y ^ 2) ≤ 1 / (2 * y)) := by
  intro h
  have bad := h 1 (-1) (by norm_num)
  have hp : 1 / (2 * (-1 : ℝ)) < (1 : ℝ) / (1 ^ 2 + (-1) ^ 2) := by
    norm_num
    exact (by norm_num : -(1 / 2 : ℝ) < ((1 : ℝ) + 1)⁻¹)
  exact (not_le_of_gt hp) bad

#print axioms solution
