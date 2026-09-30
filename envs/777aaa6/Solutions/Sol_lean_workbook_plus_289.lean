-- Prove2me | solution 1 for lean_workbook_plus_289
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:20.957142+00:00
-- url     : https://prove2.me/submissions/8bf1ba0a-677b-42d9-84f7-7d6a966248aa

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) :
  a^4 * b^2 + b^4 * c^2 ≥ 2 * b^3 * a^2 * c ∧
  a^4 * b^2 + c^4 * a^2 ≥ 2 * a^3 * c^2 * b ∧
  b^4 * c^2 + c^4 * a^2 ≥ 2 * c^3 * b^2 * a   := by
  constructor
  · nlinarith [sq_nonneg (a ^ 2 * b - b ^ 2 * c)]
  constructor
  · nlinarith [sq_nonneg (a ^ 2 * b - c ^ 2 * a)]
  · nlinarith [sq_nonneg (b ^ 2 * c - c ^ 2 * a)]

#print axioms solution
