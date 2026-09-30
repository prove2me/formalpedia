-- Prove2me | solution 1 for lean_workbook_plus_75536
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:19.734318+00:00
-- url     : https://prove2.me/submissions/beababc7-2518-43ee-9390-ccfbe0226047

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (u : ℝ) : Real.sqrt (1 - u) ≤ |1 - 1 / 2 * u| := by
  apply (Real.sqrt_le_left (abs_nonneg _)).2
  rw [sq_abs]
  nlinarith only [sq_nonneg u]
