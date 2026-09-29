-- Prove2me | solution 1 for lean_workbook_plus_42467
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-04-10T18:17:51.358861+00:00
-- url     : https://prove2.me/submissions/44411410-bec5-4215-8b89-6ef2e2979caa

import Theorems.Thm_lean_workbook_plus_42467
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) :
    a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ (3 / 4) * (a - b)^2 := by
  nlinarith [sq_nonneg (a + b - 2*c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
