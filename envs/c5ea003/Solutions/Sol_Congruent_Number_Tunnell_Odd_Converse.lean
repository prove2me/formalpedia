-- Prove2me | solution 1 for Congruent_Number_Tunnell_Odd_Converse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:30:42.791348+00:00
-- url     : https://prove2.me/submissions/3faea05a-324f-4f6c-98ee-37f36510cc5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_CongruentNumber_rational_triangle_iff_curve_point
import Theorems.Thm_Tunnell_odd_count_implies_curve_point

theorem solution (n : ℕ) (hsqf : Squarefree n) (hodd : Odd n) :
    2 * ({(x,y,z) : ℤ × ℤ × ℤ | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2} : Set (ℤ × ℤ × ℤ)).ncard =
      ({(x,y,z) : ℤ × ℤ × ℤ | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2} : Set (ℤ × ℤ × ℤ)).ncard →
    ∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ (n : ℚ) = (2⁻¹ : ℚ) * a * b := by
  intro hcount
  have hn : 0 < (n : ℚ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hsqf.ne_zero)
  exact (CongruentNumber.rational_triangle_iff_curve_point (n : ℚ) hn).mpr
    (Tunnell.odd_count_implies_curve_point n hsqf hodd hcount)
