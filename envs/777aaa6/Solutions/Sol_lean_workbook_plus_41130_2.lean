-- Prove2me | solution 2 for lean_workbook_plus_41130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:37.357818+00:00
-- url     : https://prove2.me/submissions/7bd3f324-ff08-4f65-b8a5-d5ff4d9d6a21

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : Real.sqrt (n * (n + 2)) < n + 1 := by
  rw [Real.sqrt_lt' (by positivity)]
  nlinarith
