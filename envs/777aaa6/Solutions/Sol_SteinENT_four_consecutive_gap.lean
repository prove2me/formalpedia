-- Prove2me | solution 1 for SteinENT.four_consecutive_gap
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:26:44.620249+00:00
-- url     : https://prove2.me/submissions/c9cbbd19-47ca-4555-a5b2-925f6057f47c

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SteinENT

theorem _root_.solution (n : ℤ) :
    ∃ k : ℤ, 0 ≤ k ∧ k < 4 ∧ ¬ ∃ x y : ℤ, n + k = x ^ 2 + y ^ 2 := by
  refine ⟨(3 - n) % 4, Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num), ?_⟩
  rintro ⟨x, y, h⟩
  have hmod : (n + (3 - n) % 4) % 4 = 3 := by omega
  rw [h, Int.add_emod, pow_two, pow_two, Int.mul_emod x x, Int.mul_emod y y] at hmod
  have hx0 := Int.emod_nonneg x (by norm_num : (4 : ℤ) ≠ 0)
  have hx1 := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 4)
  have hy0 := Int.emod_nonneg y (by norm_num : (4 : ℤ) ≠ 0)
  have hy1 := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 4)
  interval_cases hx : x % 4 <;> interval_cases hy : y % 4 <;>
    norm_num [hx, hy] at hmod

end SteinENT
