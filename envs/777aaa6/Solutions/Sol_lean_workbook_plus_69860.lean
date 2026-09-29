-- Prove2me | solution 1 for lean_workbook_plus_69860
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:03.705987+00:00
-- url     : https://prove2.me/submissions/c9079e95-0004-4397-923b-e51552c66cda

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x : ℝ) : x^2 - x - 1 = 0 ↔ x = (1 + Real.sqrt 5)/2 ∨ x = (1 - Real.sqrt 5)/2 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hp : (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith
