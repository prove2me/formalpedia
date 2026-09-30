-- Prove2me | solution 1 for lean_workbook_plus_68207
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:18:39.541004+00:00
-- url     : https://prove2.me/submissions/a7a3177b-b7f7-4c4e-a683-f8ef2dd77224

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

private theorem quadratic_nonneg (u : ℝ) : 0 ≤ u ^ 2 - u + 1 := by
  nlinarith [sq_nonneg (u - 1 / 2)]

theorem solution (a b c : ℝ) :
    (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≥
      (a + b) * (b + c) * (c + a) +
        (1 / 3) * (a * b + b * c + c * a - a - b - c) ^ 2 := by
  have h1 := mul_nonneg (sq_nonneg (a - b)) (quadratic_nonneg c)
  have h2 := mul_nonneg (sq_nonneg (b - c)) (quadratic_nonneg a)
  have h3 := mul_nonneg (sq_nonneg (c - a)) (quadratic_nonneg b)
  nlinarith [sq_nonneg (a * b * c - 1), h1, h2, h3]
