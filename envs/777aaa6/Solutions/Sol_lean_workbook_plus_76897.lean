-- Prove2me | solution 1 for lean_workbook_plus_76897
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:41.847861+00:00
-- url     : https://prove2.me/submissions/e749e869-c484-4b2b-964c-9d56b9801ea2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) ≥
    a ^ 3 * b + a ^ 3 * c + b ^ 3 * a + b ^ 3 * c + c ^ 3 * a + c ^ 3 * b := by
  have h (x y : ℝ) : 0 ≤ (x - y) ^ 2 * (x ^ 2 + x * y + y ^ 2) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  nlinarith [h a b, h b c, h c a]
