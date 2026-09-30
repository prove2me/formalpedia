-- Prove2me | solution 1 for lean_workbook_plus_80393
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:55.624173+00:00
-- url     : https://prove2.me/submissions/d677e549-69fd-4f41-969f-5ea0bd0eb9e9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (x y z : ℝ) :
    x^2 + y^2 + z^2 = x * y + y * z + z * x ↔ x = y ∧ y = z ∧ z = x := by
  constructor
  · intro h
    have hxy : (x-y)^2 = 0 := by
      nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
    have hyz : (y-z)^2 = 0 := by
      nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
    have heq1 : x = y := sub_eq_zero.mp (sq_eq_zero_iff.mp hxy)
    have heq2 : y = z := sub_eq_zero.mp (sq_eq_zero_iff.mp hyz)
    exact ⟨heq1, heq2, (heq1.trans heq2).symm⟩
  · rintro ⟨rfl, rfl, _⟩
    ring
