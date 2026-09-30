-- Prove2me | solution 1 for lean_workbook_plus_11890
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:12:46.516606+00:00
-- url     : https://prove2.me/submissions/8d8fb825-764d-4f04-b094-d6b0f1971989

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℕ → ℝ) (n : ℕ) : a n = (n^2 + 2*n + 1) / (n^2 + n) → a n ≠ 1 ∨ a n = 1 := by
  intro _
  exact (em (a n = 1)).symm
