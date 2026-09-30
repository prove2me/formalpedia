-- Prove2me | solution 1 for lean_workbook_plus_82401
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:04.905521+00:00
-- url     : https://prove2.me/submissions/920ebf2a-03ec-4420-a0a7-9d51079a4ee2

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x, 15*f x = 3*x+3) :
    ∀ x, f x = 1/5*x+1/5 := by
  intro x
  linarith [hf x]

#print axioms solution
