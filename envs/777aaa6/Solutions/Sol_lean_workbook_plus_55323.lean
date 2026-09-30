-- Prove2me | solution 1 for lean_workbook_plus_55323
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:03:44.128316+00:00
-- url     : https://prove2.me/submissions/8302731a-6f8f-4152-8870-36fd384578ee

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem quintic_cubic_gap (a : ℝ) :
    a ^ 5 - a ^ 3 + a - a ^ 3 = a * (a ^ 2 - 1) ^ 2 := by
  ring

theorem quintic_equation_strict_cube (a : ℝ) (ha : 0 < a)
    (he : a ^ 5 - a ^ 3 + a = 2) : a ^ 3 < 2 := by
  have hn : a ^ 2 - 1 ≠ 0 := by
    intro hz
    have ha1 : a = 1 := by nlinarith
    rw [ha1] at he
    norm_num at he
  have hp := mul_pos ha (sq_pos_of_ne_zero hn)
  linarith [quintic_cubic_gap a]

theorem solution (a : ℝ) (h₁ : a > 0) (h₂ : a ^ 5 - a ^ 3 + a = 2) :
    a ^ 3 ≤ 2 :=
  (quintic_equation_strict_cube a h₁ h₂).le

#print axioms solution
#print axioms quintic_equation_strict_cube
