-- Prove2me | solution 1 for lean_workbook_plus_76017
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:26:47.47561+00:00
-- url     : https://prove2.me/submissions/fc65bd54-48eb-4228-b8bc-64e875355e85

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ k : ℝ, k > 0 →
    1 / (Real.sqrt k + Real.sqrt (k + 1)) = Real.sqrt (k + 1) - Real.sqrt k := by
  intro k hk
  have hk1 : 0 ≤ k + 1 := by linarith
  have hsq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
  have hsq1 : Real.sqrt (k + 1) ^ 2 = k + 1 := Real.sq_sqrt hk1
  have hd : Real.sqrt k + Real.sqrt (k + 1) ≠ 0 := by
    have : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
    linarith [Real.sqrt_nonneg (k + 1)]
  apply (div_eq_iff hd).2
  nlinarith

#print axioms solution
