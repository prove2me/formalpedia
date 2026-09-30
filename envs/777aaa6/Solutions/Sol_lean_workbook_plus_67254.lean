-- Prove2me | solution 1 for lean_workbook_plus_67254
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:53:40.059285+00:00
-- url     : https://prove2.me/submissions/ef00c781-2ffb-4349-a0c2-0fa6bc059771

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (u : ℝ) (hu : u = (1 + Real.sqrt 5) / 2) : u ^ 2 = u + 1 := by
  rw [hu]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

#print axioms solution
