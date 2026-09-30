-- Prove2me | solution 1 for lean_workbook_plus_76620
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:17.43001+00:00
-- url     : https://prove2.me/submissions/f8a09475-5af3-484f-b742-173a7eca15d4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c x y z : ℝ) (h₁ : a ≥ b ∧ b ≥ c)
    (h₂ : x ≥ y ∧ y ≥ z) (h₃ : x + y + z = 0) : a * x + b * y + c * z ≥ 0 := by
  have hx : 0 ≤ x := by linarith only [h₂.1, h₂.2, h₃]
  have hz : 0 ≤ -z := by linarith only [h₂.1, h₂.2, h₃]
  have hid : a*x + b*y + c*z = (a-b)*x + (b-c)*(-z) := by
    nlinarith only [congrArg (fun t : ℝ => b*t) h₃]
  rw [hid]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr h₁.1) hx)
    (mul_nonneg (sub_nonneg.mpr h₁.2) hz)
