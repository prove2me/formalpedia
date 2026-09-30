-- Prove2me | solution 1 for lean_workbook_plus_25992
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:06:03.091356+00:00
-- url     : https://prove2.me/submissions/54bb0854-dba7-45e6-a535-699c0097efd5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) : a * b ^ 2 ≤ 4 / 27 := by
  have hae : a = 1 - b := by linarith
  rw [hae]
  have hp : 0 ≤ 3 * b + 1 := by linarith
  nlinarith [mul_nonneg (sq_nonneg (3 * b - 2)) hp]
