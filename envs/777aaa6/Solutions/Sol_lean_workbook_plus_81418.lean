-- Prove2me | solution 1 for lean_workbook_plus_81418
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:45.150735+00:00
-- url     : https://prove2.me/submissions/1d968c52-a94f-43af-8df1-9a7aed633e26

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (f : ℝ → ℝ)
    (f_def : ∀ x, f x = 2 * x^3 - 12 * x^2 + 23 * x - 12) : f 5 = 53 := by
  rw [f_def]
  norm_num
