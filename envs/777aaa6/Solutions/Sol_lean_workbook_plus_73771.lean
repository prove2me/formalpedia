-- Prove2me | solution 1 for lean_workbook_plus_73771
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:49:54.244477+00:00
-- url     : https://prove2.me/submissions/33ad054a-c82e-4780-87f0-d4effca47f70

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : 7 < Real.sqrt 50 ∧ Real.sqrt 50 < 8 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 50)
  have hn := Real.sqrt_nonneg 50
  constructor <;> nlinarith

#print axioms solution
