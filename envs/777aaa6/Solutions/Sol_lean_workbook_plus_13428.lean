-- Prove2me | solution 1 for lean_workbook_plus_13428
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:43.791489+00:00
-- url     : https://prove2.me/submissions/383ddd6b-a2a9-49a7-ab0c-45a7d13bcc73

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d e f : ℝ) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) + Real.sqrt ((a - e) ^ 2 + (b - f) ^ 2) ≥ Real.sqrt ((e - a) ^ 2 + (f - b) ^ 2) := by
  have h : (e - a) ^ 2 + (f - b) ^ 2 = (a - e) ^ 2 + (b - f) ^ 2 := by ring
  rw [h]
  have := Real.sqrt_nonneg ((a - c) ^ 2 + (b - d) ^ 2)
  linarith
