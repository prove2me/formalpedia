-- Prove2me | solution 1 for lean_workbook_plus_79483
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:15.819048+00:00
-- url     : https://prove2.me/submissions/a3302dce-78d1-4358-9577-6fb8bed7df07

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ x y z : ℝ,
    x ≥ y ∧ y ≥ z ∧ 3 * x ^ 4 ≥ x ^ 4 + y ^ 4 + z ^ 4 ∧
    x ^ 4 + y ^ 4 + z ^ 4 = 1 → x ^ 2 ≥ Real.sqrt 3 / 3 := by
  intro x y z h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsq : (Real.sqrt 3 / 3) ^ 2 ≤ (x ^ 2) ^ 2 := by
    nlinarith [h.2.2.1, h.2.2.2]
  exact (sq_le_sq₀ (by positivity) (sq_nonneg x)).mp hsq

#print axioms solution
