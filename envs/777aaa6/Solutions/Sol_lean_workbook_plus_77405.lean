-- Prove2me | solution 1 for lean_workbook_plus_77405
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:50.334913+00:00
-- url     : https://prove2.me/submissions/2fb1a169-dfdf-4fdd-9ef7-ae5bebbb5c75

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (x : ℝ) : x^2 - 4*x - 165 = 0 ↔ x = 15 ∨ x = -11 := by
  have hfactor : x^2 - 4*x - 165 = (x-15)*(x+11) := by ring
  rw [hfactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
