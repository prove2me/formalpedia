-- Prove2me | solution 1 for lean_workbook_plus_67693
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:58:52.834917+00:00
-- url     : https://prove2.me/submissions/f9398677-632f-4f08-a725-4c625c56d4f2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem source_bounds (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a+b)*(2*b+c)*(2*c+a) ≥ (1/2)*(a+2*b+2*c)*(a*b+2*b*c+2*c*a) ∧
    (a+b)*(2*b+c)*(2*c+a) ≥ (1/3)*(a+2*b+2*c)*(a*b+3*b*c+3*c*a) := by
  have h1 := mul_nonneg (sq_nonneg a) (le_of_lt hb)
  have h2 := mul_nonneg (le_of_lt ha) (sq_nonneg b)
  have h3 := mul_nonneg (sq_nonneg b) (le_of_lt hc)
  have h4 := le_of_lt (mul_pos (mul_pos ha hb) hc)
  constructor <;> nlinarith only [h1, h2, h3, h4]

theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 →
    (a+b)*(2*b+c)*(2*c+a) ≥ (1/2)*(a+2*b+2*c)*(a*b+2*b*c+2*c*a) := by
  intro a b c h
  exact (source_bounds a b c h.1 h.2.1 h.2.2).1
