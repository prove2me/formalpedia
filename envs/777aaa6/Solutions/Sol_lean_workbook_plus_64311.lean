-- Prove2me | solution 1 for lean_workbook_plus_64311
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:04.10264+00:00
-- url     : https://prove2.me/submissions/80351dec-b405-44ea-a762-b74b8faa543a

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace CubicCongruenceMinimum

theorem roots_seven (z : ℤ)
    (h : z ^ 3 + 2 * z ^ 2 + 5 * z + 3 ≡ 0 [ZMOD 7]) :
    z % 7 = 3 ∨ z % 7 = 4 ∨ z % 7 = 5 := by
  have hz := Int.mod_modEq z 7
  have hp := (((hz.pow 3).add ((hz.pow 2).mul_left 2)).add
    (hz.mul_left 5)).add_right 3
  have hh := hp.trans h
  have h0 := Int.emod_nonneg z (by decide : (7 : ℤ) ≠ 0)
  have h7 := Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 7)
  interval_cases hr : z % 7 <;> norm_num [hr, Int.ModEq] at hh <;> norm_num [hr]

theorem roots_eleven (z : ℤ)
    (h : z ^ 3 + 8 * z ^ 2 + 2 * z ≡ 0 [ZMOD 11]) :
    z % 11 = 0 ∨ z % 11 = 1 ∨ z % 11 = 2 := by
  have hz := Int.mod_modEq z 11
  have hp := ((hz.pow 3).add ((hz.pow 2).mul_left 8)).add (hz.mul_left 2)
  have hh := hp.trans h
  have h0 := Int.emod_nonneg z (by decide : (11 : ℤ) ≠ 0)
  have h11 := Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 11)
  interval_cases hr : z % 11 <;> norm_num [hr, Int.ModEq] at hh <;> norm_num [hr]

theorem roots_thirteen (z : ℤ)
    (h : z ^ 3 + 4 * z ^ 2 - 11 ≡ 0 [ZMOD 13]) :
    z % 13 = 2 ∨ z % 13 = 3 ∨ z % 13 = 4 := by
  have hz := Int.mod_modEq z 13
  have hp := ((hz.pow 3).add ((hz.pow 2).mul_left 4)).sub_right 11
  have hh := hp.trans h
  have h0 := Int.emod_nonneg z (by decide : (13 : ℤ) ≠ 0)
  have h13 := Int.emod_lt_of_pos z (by decide : (0 : ℤ) < 13)
  interval_cases hr : z % 13 <;> norm_num [hr, Int.ModEq] at hh <;> norm_num [hr]

theorem attained :
    (67 : ℤ) ^ 3 + 2 * 67 ^ 2 + 5 * 67 + 3 ≡ 0 [ZMOD 7] ∧
    (67 : ℤ) ^ 3 + 8 * 67 ^ 2 + 2 * 67 ≡ 0 [ZMOD 11] ∧
    (67 : ℤ) ^ 3 + 4 * 67 ^ 2 - 11 ≡ 0 [ZMOD 13] := by
  norm_num [Int.ModEq]

end CubicCongruenceMinimum

theorem solution (x : ℕ) (h₀ : 0 < x)
    (h₁ : x ^ 3 + 2 * x ^ 2 + 5 * x + 3 ≡ 0 [ZMOD 7])
    (h₂ : x ^ 3 + 8 * x ^ 2 + 2 * x ≡ 0 [ZMOD 11])
    (h₃ : x ^ 3 + 4 * x ^ 2 - 11 ≡ 0 [ZMOD 13]) : 67 ≤ x := by
  obtain h7 | h7 | h7 := CubicCongruenceMinimum.roots_seven x h₁ <;>
    obtain h11 | h11 | h11 := CubicCongruenceMinimum.roots_eleven x h₂ <;>
    obtain h13 | h13 | h13 := CubicCongruenceMinimum.roots_thirteen x h₃ <;>
    omega

#print axioms CubicCongruenceMinimum.attained
#print axioms solution
