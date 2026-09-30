-- Prove2me | solution 1 for lean_workbook_plus_75448
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:52:21.295914+00:00
-- url     : https://prove2.me/submissions/d14eae99-441b-4d9e-8a17-dff92beee30f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : 11 / 2 < (11 + 2 * Real.sqrt 30) / 2 ∧
    (11 + 2 * Real.sqrt 30) / 2 < 23 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)
  have hp : 0 < Real.sqrt 30 := Real.sqrt_pos.mpr (by norm_num)
  constructor <;> nlinarith

#print axioms solution
