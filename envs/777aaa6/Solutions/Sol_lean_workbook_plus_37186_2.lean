-- Prove2me | solution 2 for lean_workbook_plus_37186
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:14.401432+00:00
-- url     : https://prove2.me/submissions/54a9665b-99b6-411c-b863-266d0353fb69

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 * b^4 + b^4 * c^4 + c^4 * a^4 ≥ a^2 * b^2 * c^2 * (a^2 + b^2 + c^2)   := by
  have h1 := sq_nonneg (a^2 * b^2 - b^2 * c^2)
  have h2 := sq_nonneg (b^2 * c^2 - c^2 * a^2)
  have h3 := sq_nonneg (c^2 * a^2 - a^2 * b^2)
  linarith

#print axioms solution
