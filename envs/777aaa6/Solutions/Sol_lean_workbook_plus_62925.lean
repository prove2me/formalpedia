-- Prove2me | solution 1 for lean_workbook_plus_62925
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:50.66116+00:00
-- url     : https://prove2.me/submissions/faa88e5e-db24-4722-a42c-7ce41547d217

import Mathlib.Analysis.Complex.Basic

theorem solution (f g : ℝ → ℝ) (f_def : ∀ x, f x = x^2 + 2 * x) (g_def : ∀ x, g x = 3 * x - 4) : f 3 + g 4 = 23 := by
  linarith [f_def 3, g_def 4]
