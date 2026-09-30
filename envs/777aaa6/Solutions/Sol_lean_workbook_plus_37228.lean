-- Prove2me | solution 1 for lean_workbook_plus_37228
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:13.102738+00:00
-- url     : https://prove2.me/submissions/aa5dbd74-1791-46d9-92d2-d295ea66677f

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : (2 * x) / (1 + x ^ 2) ≤ 1   := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
  nlinarith [sq_nonneg (x - 1)]

#print axioms solution
