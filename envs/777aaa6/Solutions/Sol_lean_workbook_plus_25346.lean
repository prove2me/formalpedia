-- Prove2me | solution 1 for lean_workbook_plus_25346
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:52.450443+00:00
-- url     : https://prove2.me/submissions/84b71026-8f33-4ea8-ad41-9d2ee0c61ce2

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ a b : ℝ, a * b * (a ^ 4 + b ^ 4) + 2 * a * b ≥ 2 * a * b * (a ^ 2 + b ^ 2)) := by
  intro h
  have bad := h 1 (-2)
  norm_num at bad
  have hb : (4 : ℝ) + 2 * (1 + 16) ≤ 4 * (1 + 4) := bad
  exact (by norm_num : ¬ ((4 : ℝ) + 2 * (1 + 16) ≤ 4 * (1 + 4))) hb

#print axioms solution
