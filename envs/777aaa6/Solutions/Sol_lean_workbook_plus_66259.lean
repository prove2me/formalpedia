-- Prove2me | solution 1 for lean_workbook_plus_66259
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:11.49095+00:00
-- url     : https://prove2.me/submissions/031272e9-120b-419c-bee8-0d79dd167bcc

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y z : ℝ, (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 ≥ 2 * (x ^ 3 + y ^ 3 + z ^ 3) + x ^ 2 + y ^ 2 + z ^ 2) := by
  intro h
  have bad := h (1 / 2) (1 / 2) (1 / 2)
  have hp : ((1 / 2 : ℝ) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2) ^ 2 <
      2 * ((1 / 2 : ℝ) ^ 3 + (1 / 2) ^ 3 + (1 / 2) ^ 3) +
      (1 / 2) ^ 2 + (1 / 2) ^ 2 + (1 / 2) ^ 2 := by norm_num
  exact (not_le_of_gt hp) bad

#print axioms solution
