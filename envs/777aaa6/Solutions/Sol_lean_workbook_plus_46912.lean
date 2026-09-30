-- Prove2me | solution 1 for lean_workbook_plus_46912
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:36.170509+00:00
-- url     : https://prove2.me/submissions/21346dac-6294-437b-afb8-12586e381cd3

import Mathlib
set_option autoImplicit false

theorem solution  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x = Real.sqrt (2 + x)) :
  x = 2   := by
  have he : x ^ 2 = 2 + x := by
    calc
      x ^ 2 = (Real.sqrt (2 + x)) ^ 2 := congrArg (fun t : ℝ => t ^ 2) h₁
      _ = 2 + x := Real.sq_sqrt (by linarith)
  have hp : (x - 2) * (x + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with ha | hb <;> linarith

#print axioms solution
