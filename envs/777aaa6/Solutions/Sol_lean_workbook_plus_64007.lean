-- Prove2me | solution 1 for lean_workbook_plus_64007
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:02.531279+00:00
-- url     : https://prove2.me/submissions/2590bd18-a50c-4d95-b4bb-43bfbb3f5fd5

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx: 1/5 ≤ x ∧ x ≤ 1) : 1/5 * (x^3 + 1/x) < 2   := by
  have hxpos : 0 < x := by linarith [hx.1]
  have hc : x ^ 3 ≤ 1 := pow_le_one₀ hxpos.le hx.2
  have hi : 1 / x ≤ 5 := (div_le_iff₀ hxpos).2 (by linarith [hx.1])
  linarith

#print axioms solution
