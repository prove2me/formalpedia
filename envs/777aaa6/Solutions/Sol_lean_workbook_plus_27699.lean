-- Prove2me | solution 1 for lean_workbook_plus_27699
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:54:37.601307+00:00
-- url     : https://prove2.me/submissions/3158baf6-1f8b-4c9b-9016-ce41d5638378

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

theorem solution (a b c : Real) (h1 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
    (h2 : a ^ 2 = b * (b + c)) (h3 : b ^ 2 = c * (c + a)) :
    1 / c = 1 / a + 1 / b := by
  obtain ⟨ha, hb, hc⟩ := h1
  have hs : a + b + c ≠ 0 := by
    intro hz
    have hbc : b + c = -a := by linarith
    have hm : a * (a + b) = 0 := by
      rw [hbc] at h2
      nlinarith [h2]
    have hab : a + b = 0 := (mul_eq_zero.mp hm).resolve_left ha
    exact hc (by linarith)
  have hm : (a + b + c) * (a * b - a * c - b * c) = 0 := by
    linear_combination b * h2 + (a + b) * h3
  have hp : a * b - a * c - b * c = 0 := (mul_eq_zero.mp hm).resolve_left hs
  field_simp
  nlinarith only [hp]

#print axioms solution
