-- Prove2me | solution 1 for lean_workbook_plus_78731
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:58.30548+00:00
-- url     : https://prove2.me/submissions/4846215d-4d65-4a74-8099-5ee7f1ad2b1d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x y z : ℝ) :
    (x + y + z) ^ 4 + 3 * (x * y + y * z + z * x) ^ 2 ≥
      4 * (x + y + z) ^ 2 * (x * y + y * z + z * x) := by
  have h1 : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 - (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h2 : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x + y + z), sq_nonneg x, sq_nonneg y, sq_nonneg z]
  nlinarith [mul_nonneg h1 h2]
