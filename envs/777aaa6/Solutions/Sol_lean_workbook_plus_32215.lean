-- Prove2me | solution 1 for lean_workbook_plus_32215
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:59.221705+00:00
-- url     : https://prove2.me/submissions/a3f099ef-4429-460b-b668-65a9a9e8ac78

import Mathlib.Analysis.Complex.Basic

theorem solution  (x : ℝ)
  (h₀ : x^3 + 1 = 2 * x) :
  x^3 - 2 * x + 1 = 0 := by
  linarith
