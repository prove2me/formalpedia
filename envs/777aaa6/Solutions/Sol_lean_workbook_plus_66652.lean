-- Prove2me | solution 1 for lean_workbook_plus_66652
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:43.323972+00:00
-- url     : https://prove2.me/submissions/969c5bc2-59e2-484b-b170-a166a81dce83

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 - 3 * a * b + 1 ≥ 0   := by
  have hp : 0 ≤ (a + b + 1) * ((a - b) ^ 2 + (a - 1) ^ 2 + (b - 1) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [hp]

#print axioms solution
