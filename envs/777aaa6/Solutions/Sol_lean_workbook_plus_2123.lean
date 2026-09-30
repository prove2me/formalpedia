-- Prove2me | solution 1 for lean_workbook_plus_2123
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:04.761627+00:00
-- url     : https://prove2.me/submissions/a20b62a9-63b4-4ad1-b891-4d1f5e27d1d3

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) : x^3 < 1 ∧ 1 < x^4 + 1   := by
  constructor
  · exact pow_lt_one₀ (le_of_lt hx.1) hx.2 (by decide)
  · have hp : 0 < x ^ 4 := pow_pos hx.1 4
    linarith

#print axioms solution
