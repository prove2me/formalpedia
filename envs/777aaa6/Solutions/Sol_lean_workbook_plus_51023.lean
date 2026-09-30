-- Prove2me | solution 1 for lean_workbook_plus_51023
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:46.149418+00:00
-- url     : https://prove2.me/submissions/cb17e524-d4a3-45e8-b2d9-b629cd265d3b

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (x+y+z-3)*((x+y+z)^2+3*(x+y+z)+36) ≥ 0 → x+y+z ≥ 3   := by
  intro x y z h
  have hp : 0 < (x + y + z) ^ 2 + 3 * (x + y + z) + 36 := by
    nlinarith only [sq_nonneg (x + y + z + 3 / 2)]
  by_contra! hs
  have hn : (x + y + z - 3) * ((x + y + z) ^ 2 + 3 * (x + y + z) + 36) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hp
  exact (not_lt_of_ge h) hn

#print axioms solution
