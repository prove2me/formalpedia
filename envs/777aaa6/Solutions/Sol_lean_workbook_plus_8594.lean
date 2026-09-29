-- Prove2me | solution 1 for lean_workbook_plus_8594
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:19.166069+00:00
-- url     : https://prove2.me/submissions/741ec184-a12d-4d05-ba90-3ec2ae33b15a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (k : ℝ) : k^2 + 3*k - 108 = 0 ↔ k = 9 ∨ k = -12 := by
  constructor
  · intro h
    have hp : (k - 9) * (k + 12) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
