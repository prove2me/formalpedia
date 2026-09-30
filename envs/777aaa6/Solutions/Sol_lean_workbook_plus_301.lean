-- Prove2me | solution 1 for lean_workbook_plus_301
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:04.246981+00:00
-- url     : https://prove2.me/submissions/8f3eb54b-4070-4365-97b3-d804d162ea62

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (a^2 + 5 * b^2) / c^2 ≥ (5:ℝ) / 24 * (3 * (5:ℝ)^(1 / 3) - 21 * (25:ℝ)^(1 / 3) - 1) := by
  have h0 : 0 ≤ (a^2 + 5 * b^2) / c^2 := by positivity
  norm_num
  linarith
