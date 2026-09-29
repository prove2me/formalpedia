-- Prove2me | solution 1 for lean_workbook_plus_20215
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-04-10T18:17:42.409521+00:00
-- url     : https://prove2.me/submissions/5064eac6-0678-4f8c-a160-9ee60d5b7f95

import Theorems.Thm_lean_workbook_plus_20215
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) : a ^ 2 - a * b + b ^ 2 ≤ (3 * (a ^ 2 + b ^ 2)) / 2 := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
