-- Prove2me | solution 1 for lean_workbook_plus_33907
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:59.84256+00:00
-- url     : https://prove2.me/submissions/a67ff9e6-ca8c-4c3f-9535-2664fd2161a4

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ c : ℝ, (4 / 3 + (4 * c * (2 - c) * (c - 1) ^ 2) / ((c ^ 2 + 2) * ((2 - c) ^ 2 + 2))) ≥ 4 / 3) := by
  intro h
  have bad := h 3
  norm_num at bad

#print axioms solution
