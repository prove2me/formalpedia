-- Prove2me | solution 1 for lean_workbook_plus_60852
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:13:57.267911+00:00
-- url     : https://prove2.me/submissions/4ac276c1-9f8f-406d-8983-fd266317ea73

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

def sixVariableQuadratic (x y z u v w : ℝ) : ℝ :=
  (x - z) * (v - z) + (y - x) * (w - x) + (u - y) * (z - y) -
    2 * (u - v) * v - 2 * (v - w) * w - 2 * (w - u) * u

theorem six_variable_quadratic_identity (x y z u v w : ℝ) :
    12 * sixVariableQuadratic x y z u v w =
      3 * (2 * x - y - z + v - w) ^ 2 +
      (3 * y - 3 * z - 2 * u + v + w) ^ 2 +
      5 * (2 * u - v - w) ^ 2 + 15 * (v - w) ^ 2 := by
  dsimp [sixVariableQuadratic]
  ring

theorem six_variable_quadratic_nonneg (x y z u v w : ℝ) :
    0 ≤ sixVariableQuadratic x y z u v w := by
  have hid := six_variable_quadratic_identity x y z u v w
  nlinarith [sq_nonneg (2 * x - y - z + v - w),
    sq_nonneg (3 * y - 3 * z - 2 * u + v + w),
    sq_nonneg (2 * u - v - w), sq_nonneg (v - w)]

theorem six_variable_quadratic_equality (x y z u v w : ℝ) :
    sixVariableQuadratic x y z u v w = 0 ↔
      x = y ∧ y = z ∧ u = v ∧ v = w := by
  constructor
  · intro he
    have hid := six_variable_quadratic_identity x y z u v w
    rw [he, mul_zero] at hid
    have ha := sq_nonneg (2 * x - y - z + v - w)
    have hb := sq_nonneg (3 * y - 3 * z - 2 * u + v + w)
    have hc := sq_nonneg (2 * u - v - w)
    have hd := sq_nonneg (v - w)
    have ha0 : 2 * x - y - z + v - w = 0 :=
      sq_eq_zero_iff.mp (by nlinarith only [hid, ha, hb, hc, hd])
    have hb0 : 3 * y - 3 * z - 2 * u + v + w = 0 :=
      sq_eq_zero_iff.mp (by nlinarith only [hid, ha, hb, hc, hd])
    have hc0 : 2 * u - v - w = 0 :=
      sq_eq_zero_iff.mp (by nlinarith only [hid, ha, hb, hc, hd])
    have hd0 : v - w = 0 :=
      sq_eq_zero_iff.mp (by nlinarith only [hid, ha, hb, hc, hd])
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [sixVariableQuadratic]

theorem solution (x y z u v w : ℝ) :
    (x - z) * (v - z) + (y - x) * (w - x) + (u - y) * (z - y) -
      2 * (u - v) * v - 2 * (v - w) * w - 2 * (w - u) * u ≥ 0 :=
  six_variable_quadratic_nonneg x y z u v w

#print axioms solution
#print axioms six_variable_quadratic_identity
#print axioms six_variable_quadratic_nonneg
#print axioms six_variable_quadratic_equality
