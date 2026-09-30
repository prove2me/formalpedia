-- Prove2me | solution 1 for lean_workbook_plus_34104
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:56.197036+00:00
-- url     : https://prove2.me/submissions/1027e35e-d4e0-494d-99ad-faa52af8a803

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ t : ℝ, -1 / 81 * (t - 3) * (t ^ 4 + 3 * t ^ 3 + 27 * t ^ 2 + 81 * t + 324) ≥ 0) := by
  intro h
  have bad := h 4
  norm_num at bad

#print axioms solution
