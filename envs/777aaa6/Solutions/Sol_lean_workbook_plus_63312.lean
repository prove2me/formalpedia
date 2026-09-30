-- Prove2me | solution 1 for lean_workbook_plus_63312
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:07:50.9934+00:00
-- url     : https://prove2.me/submissions/220f48a7-e180-44d5-b7e9-ddd92e1581df

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) (x : ℝ) :
    x^4-4*x^3-9*x^2+36*x = 0 ↔ x = -3 ∨ x = 0 ∨ x = 3 ∨ x = 4 := by
  have hfactor : x^4-4*x^3-9*x^2+36*x = (x+3)*x*(x-3)*(x-4) := by ring
  rw [hfactor]
  simp only [mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_assoc]
