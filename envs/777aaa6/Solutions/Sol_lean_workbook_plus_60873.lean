-- Prove2me | solution 1 for lean_workbook_plus_60873
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:53:21.282254+00:00
-- url     : https://prove2.me/submissions/bc154c16-8568-49ac-b501-5f8be77ac7a7

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (x : ℝ) (hx : x > -1) : (1 + x) ^ n ≥ 1 + n * x   := by
  exact one_add_mul_le_pow (show (-2 : ℝ) ≤ x by linarith only [hx]) n

#print axioms solution
