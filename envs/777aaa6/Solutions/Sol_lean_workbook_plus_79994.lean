-- Prove2me | solution 1 for lean_workbook_plus_79994
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:12:58.475348+00:00
-- url     : https://prove2.me/submissions/674b0a18-3e1d-4f6c-a7df-995ca5a47f69

import Mathlib
set_option autoImplicit false

theorem solution (z : ℂ) (h₀ : (z + 2)^2 = 0) : z = -2 := by
  have hz : z + 2 = 0 := pow_eq_zero h₀
  linear_combination hz

#print axioms solution
