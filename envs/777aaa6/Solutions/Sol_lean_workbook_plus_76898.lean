-- Prove2me | solution 1 for lean_workbook_plus_76898
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:42.560918+00:00
-- url     : https://prove2.me/submissions/4a3c25f9-8183-4f07-8d7c-4b25c87fdab3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥
    |(a - b) * (b - c)| + |(b - c) * (c - a)| + |(c - a) * (a - b)| := by
  have h (x y : ℝ) : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  nlinarith [h (a - b) (b - c), h (b - c) (c - a), h (c - a) (a - b)]
