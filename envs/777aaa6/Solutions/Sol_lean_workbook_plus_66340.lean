-- Prove2me | solution 1 for lean_workbook_plus_66340
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:37.454393+00:00
-- url     : https://prove2.me/submissions/9cad441e-b63b-4664-9cd2-5b50ce311e2e

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ (x y z : ℤ), x + y + z = 96 → x = 6 * z → z = y - 40 → |x - y| = 64) := by
  intro h
  have bad := h 42 47 7 (by norm_num) (by norm_num) (by norm_num)
  norm_num at bad

#print axioms solution
