-- Prove2me | solution 1 for lean_workbook_plus_27881
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:40:07.964174+00:00
-- url     : https://prove2.me/submissions/993afb3c-1497-49bf-898b-04dcde47fa5b

import Mathlib

set_option autoImplicit false

theorem solution (x : Real) (hx : x ≥ 1) : 8 * x ^ 3 - 25 * x ^ 2 + 4 * x + 28 ≥ 0 := by
  have hf : 8 * x ^ 3 - 25 * x ^ 2 + 4 * x + 28 = (x - 2) ^ 2 * (8 * x + 7) := by
    ring
  rw [hf]
  exact mul_nonneg (sq_nonneg _) (by linarith)

#print axioms solution
