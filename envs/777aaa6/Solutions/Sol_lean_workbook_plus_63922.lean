-- Prove2me | solution 1 for lean_workbook_plus_63922
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:31:40.995572+00:00
-- url     : https://prove2.me/submissions/bd885d2c-0b12-4fe4-a2af-eabbe5a2309a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) : x ^ 2 + 6 * x = 3 ↔
    x = -3 + 2 * Real.sqrt 3 ∨ x = -3 - 2 * Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor
  · intro hx
    have hp : (x + 3 - 2 * Real.sqrt 3) * (x + 3 + 2 * Real.sqrt 3) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (hx | hx) <;> rw [hx] <;> nlinarith

#print axioms solution
