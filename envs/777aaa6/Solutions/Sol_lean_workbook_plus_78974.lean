-- Prove2me | solution 1 for lean_workbook_plus_78974
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:56.708099+00:00
-- url     : https://prove2.me/submissions/28768906-e0e5-4e7a-bfa8-23811791dffd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution (x y z : ℝ) :
    2 * (x ^ 4 + y ^ 4 + z ^ 4) + 7 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥
      3 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) +
        3 * (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y) := by
  have hcyclic : 3 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) ≤
      (3 / 2) * (x ^ 4 + y ^ 4 + z ^ 4 + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) := by
    nlinarith [sq_nonneg (x ^ 2 - x * y), sq_nonneg (y ^ 2 - y * z),
      sq_nonneg (z ^ 2 - z * x)]
  have hmixed : 3 * (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y) ≤
      3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
      sq_nonneg (z * x - x * y)]
  have hfourth : 0 ≤ x ^ 4 + y ^ 4 + z ^ 4 := by positivity
  have hpairs : 0 ≤ x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2 := by positivity
  nlinarith
