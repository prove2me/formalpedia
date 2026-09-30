-- Prove2me | solution 1 for lean_workbook_plus_11282
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:47:03.950132+00:00
-- url     : https://prove2.me/submissions/58463860-22e4-45a8-8a7f-59777f0600c2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace QuadraticEightObstruction

theorem square_residues (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have hnonneg : 0 ≤ x % 8 := Int.emod_nonneg x (by decide)
  have hlt : x % 8 < 8 := Int.emod_lt_of_pos x (by decide)
  have hcases : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  have hreduce : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by
    rw [pow_two, Int.mul_emod, pow_two]
  rw [hreduce]
  rcases hcases with h | h | h | h | h | h | h | h <;> norm_num [h]

theorem integer_obstruction (x y z : ℤ) : x ^ 2 + 8 * y ≠ 3 + 2 * z ^ 2 := by
  intro h
  rcases square_residues x with hx | hx | hx <;>
    rcases square_residues z with hz | hz | hz <;> omega

end QuadraticEightObstruction

theorem solution (x y z : ℕ) (_h₁ : 0 < x ∧ 0 < y ∧ 0 < z)
    (h₂ : x ^ 2 + 8 * y = 3 + 2 * z ^ 2) : False := by
  exact QuadraticEightObstruction.integer_obstruction (x : ℤ) (y : ℤ) (z : ℤ)
    (by exact_mod_cast h₂)
