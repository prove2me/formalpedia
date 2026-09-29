-- Prove2me | solution 1 for lean_workbook_plus_41546
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:22:34.557926+00:00
-- url     : https://prove2.me/submissions/b545daab-facf-40f5-abac-144f9e7c6e93

import Theorems.Thm_lean_workbook_plus_41546
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (a c : ℝ) : c^2 * (3 * a^2 + 1 - 3 * a) + c * (a - 3 * a^2) + a^2 ≥ 0 := by
  nlinarith [sq_nonneg (2 * (3 * a^2 - 3 * a + 1) * c + a - 3 * a^2),
             mul_nonneg (sq_nonneg a) (sq_nonneg (a - 1)),
             sq_nonneg (2 * a - 1), sq_nonneg a, sq_nonneg (a - 1), sq_nonneg c]
