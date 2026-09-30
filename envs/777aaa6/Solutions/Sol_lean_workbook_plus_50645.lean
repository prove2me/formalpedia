-- Prove2me | solution 1 for lean_workbook_plus_50645
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:54.791707+00:00
-- url     : https://prove2.me/submissions/3b6bdad2-c151-48a9-8718-c4816a0b18fe

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x : ℝ, x ≠ 4 ∧ x ≠ 5 → x / (x - 4) / (x - 5) = 5 / (x - 5) - 1 / (x - 4)) := by
  intro h
  have bad := h 0 (by norm_num)
  have hp : (0 : ℝ) / (0 - 4) / (0 - 5) ≠ 5 / (0 - 5) - 1 / (0 - 4) := by norm_num
  exact hp bad

#print axioms solution
