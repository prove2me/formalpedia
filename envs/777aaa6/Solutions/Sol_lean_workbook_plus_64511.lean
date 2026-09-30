-- Prove2me | solution 1 for lean_workbook_plus_64511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:23.419538+00:00
-- url     : https://prove2.me/submissions/d6d29689-3db8-43f1-a8d6-4a896f5b0ae0

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a * b * c = 1) :
  a^2 + b^2 + c^2 + a * b + b * c + a * c + 6 ≥ 4 * (a + b + c)   := by
  have h1 := sq_nonneg (a + b + c - 3)
  have h2 := sq_nonneg (a - b)
  have h3 := sq_nonneg (b - c)
  have h4 := sq_nonneg (a - c)
  linarith

#print axioms solution
