-- Prove2me | solution 1 for lean_workbook_plus_42708
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:42:23.549499+00:00
-- url     : https://prove2.me/submissions/2eb18a68-d95b-4d43-97e2-7ba637bcadb6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 →
    a ^ 2 + 2 * b ^ 2 + c ^ 2 ≥ (2 * Real.sqrt 3) / 3 * (a + 2 * b) * c := by
  intro a b c h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsa : (Real.sqrt 3 * a) ^ 2 = 3 * a ^ 2 := by rw [mul_pow, hs]
  have hsb : (Real.sqrt 3 * b) ^ 2 = 3 * b ^ 2 := by rw [mul_pow, hs]
  nlinarith [sq_nonneg (Real.sqrt 3 * a - c), sq_nonneg (Real.sqrt 3 * b - c)]

#print axioms solution
