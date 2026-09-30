-- Prove2me | solution 1 for lean_workbook_plus_23526
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:58:17.824742+00:00
-- url     : https://prove2.me/submissions/0147cc32-6e79-4423-85f2-08fdc371fa92

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^2 ≥ a^4 + b^3) : a^3 + b^3 ≤ 2   := by
  have h1 : 0 <= (a - 1)^2 * (3 * a^2 + 2 * a + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have h2 : 0 <= (b - 1)^2 * (2 * b + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hid : 3 * (a^4 - a^3 + b^3 - b^2) - (a^3 + b^3 - 2) =
      (a - 1)^2 * (3 * a^2 + 2 * a + 1) + (b - 1)^2 * (2 * b + 1) := by ring
  linarith only [hab, h1, h2, hid]

#print axioms solution
