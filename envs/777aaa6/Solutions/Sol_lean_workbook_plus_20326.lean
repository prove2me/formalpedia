-- Prove2me | solution 1 for lean_workbook_plus_20326
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:13.082063+00:00
-- url     : https://prove2.me/submissions/206c08ad-2233-4699-9cbc-fa95dbb09965

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 / 4   := by
  constructor
  exact mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have := sq_nonneg (1 - 2 * x)
  nlinarith

#print axioms solution
