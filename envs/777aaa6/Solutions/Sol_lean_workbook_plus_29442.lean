-- Prove2me | solution 1 for lean_workbook_plus_29442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:03.066083+00:00
-- url     : https://prove2.me/submissions/5b5d15d7-26c9-4fb8-b18f-69b766e0fa66

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b * (a + b - 10) + 8 * (a + b) ≥ 8   := by
  by_cases hs : 10 ≤ a + b
  · have hp : 0 ≤ a * b * (a + b - 10) :=
      mul_nonneg (mul_nonneg (by linarith only [ha]) (by linarith only [hb])) (by linarith only [hs])
    nlinarith only [hp, hs]
  · have hp : 0 ≤ (10 - (a + b)) * (a - b) ^ 2 :=
      mul_nonneg (by linarith only [hs]) (sq_nonneg (a - b))
    have hq : 0 ≤ (a + b - 2) * (a + b - 4) ^ 2 :=
      mul_nonneg (by linarith only [ha, hb]) (sq_nonneg (a + b - 4))
    nlinarith only [hp, hq]

#print axioms solution
