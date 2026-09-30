-- Prove2me | solution 1 for lean_workbook_plus_2064
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:06.215638+00:00
-- url     : https://prove2.me/submissions/1ef66398-d9ca-4221-827a-358496d90c3e

import Mathlib
set_option autoImplicit false

theorem solution : ∀ y : ℝ, y > 0 → y ^ 3 - y ^ 2 + 2 / 9 > 0   := by
  intro y hy
  have hp : 0 ≤ (y - 2 / 3) ^ 2 * (y + 1 / 3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith only [hp]

#print axioms solution
