-- Prove2me | solution 1 for lean_workbook_plus_77476
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:25:37.211956+00:00
-- url     : https://prove2.me/submissions/8e9ff3d0-245e-48a2-a491-d15dd47c563e

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace IntegerCubicNoSolutions

theorem square_mod_four (z : ℤ) : z ^ 2 % 4 = z % 2 := by
  have h0 := Int.emod_nonneg z (by decide : (4 : ℤ) ≠ 0)
  have h4 := Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 4)
  rw [pow_two, Int.mul_emod]
  interval_cases h : z % 4 <;> norm_num [h] <;> omega

theorem impossible (x y : ℤ)
    (h : x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 =
      4 * (x ^ 2 + y ^ 2 + x * y + 3)) : False := by
  set s := x + y with hs
  set t := x ^ 2 + y ^ 2 with ht
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have heq : (s - 2) * t = 2 * s ^ 2 + 12 := by
    dsimp [s, t]
    nlinarith [h]
  have hst : s ^ 2 ≤ 2 * t := by
    dsimp [s, t]
    nlinarith [sq_nonneg (x - y)]
  have hlo : 3 ≤ s := by
    by_contra hn
    have hn' : s - 2 ≤ 0 := by omega
    have hp := mul_nonpos_of_nonpos_of_nonneg hn' ht0
    nlinarith [sq_nonneg s]
  have hhi : s ≤ 6 := by
    by_contra hn
    have h7 : 0 ≤ s - 7 := by omega
    have h2 : 0 ≤ s - 2 := by omega
    have hp := mul_nonneg h2 (show 0 ≤ 2 * t - s ^ 2 by omega)
    have hq := mul_nonneg h7 (sq_nonneg s)
    nlinarith [sq_nonneg (s - 7)]
  have hx := square_mod_four x
  have hy := square_mod_four y
  have hm := Int.add_emod (x ^ 2) (y ^ 2) 4
  interval_cases s
  · have ht30 : t = 30 := by nlinarith [heq]
    rw [← ht, ht30, hx, hy] at hm
    omega
  · have hseven : (x - 2) ^ 2 = 7 := by nlinarith [heq]
    have hm7 := square_mod_four (x - 2)
    rw [hseven] at hm7
    omega
  · omega
  · have ht21 : t = 21 := by nlinarith [heq]
    rw [← ht, ht21, hx, hy] at hm
    omega

end IntegerCubicNoSolutions

theorem solution (x y : ℤ)
    (h : x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 =
      4 * (x ^ 2 + y ^ 2 + x * y + 3)) :
    (x = 2 ∧ y = 2) ∨ (x = -2 ∧ y = -2) ∨
      (x = 0 ∧ y = -3) ∨ (x = -3 ∧ y = 0) := by
  exact False.elim (IntegerCubicNoSolutions.impossible x y h)

#print axioms IntegerCubicNoSolutions.impossible
#print axioms solution
