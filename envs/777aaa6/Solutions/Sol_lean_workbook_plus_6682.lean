-- Prove2me | solution 1 for lean_workbook_plus_6682
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:03.055129+00:00
-- url     : https://prove2.me/submissions/fd572a60-a34a-4300-9ce1-15cba51c6415

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y z : ℝ, 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)) := by
  intro h
  have hb := h (-1) (-1) (-2)
  norm_num at hb

#print axioms solution
