-- Prove2me | solution 1 for lean_workbook_plus_71799
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:02:03.377016+00:00
-- url     : https://prove2.me/submissions/ed225c7e-9aa7-4ee7-a55f-639fa9f8e892

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b = a + (a + b) / 7) :
  a / b = 3 / 4 := by
  apply (div_eq_iff (ne_of_gt h₀.2)).2
  linarith
