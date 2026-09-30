-- Prove2me | solution 1 for lean_workbook_plus_78570
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T20:12:04.297929+00:00
-- url     : https://prove2.me/submissions/7648aedf-529a-4104-9015-0ccb12d0824d

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y z : ℝ, (-x^2*y^2 + (x + y)^3*z)*(x - y)^2 + (-y^2*z^2 + (y + z)^3*x)*(y - z)^2 + (-z^2*x^2 + (z + x)^3*y)*(z - x)^2 ≥ (3 + 2*Real.sqrt 2)*(x - y)^2*(y - z)^2*(z - x)^2) := by
  intro h
  have bad := h 1 (-1) 2
  norm_num at bad
  have hnonneg : (0 : Real) ≤ (3 + 2 * Real.sqrt 2) * 4 * 9 * 1 := by positivity
  have hb : (0 : Real) ≤ -62 := le_trans hnonneg bad
  have hn : ¬ ((0 : Real) ≤ -62) := by norm_num
  exact hn hb

#print axioms solution
