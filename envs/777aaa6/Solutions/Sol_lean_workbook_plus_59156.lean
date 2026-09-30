-- Prove2me | solution 1 for lean_workbook_plus_59156
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:34:46.942933+00:00
-- url     : https://prove2.me/submissions/a9122d7b-f720-4777-be36-b9956867649f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ a b : ℝ, a > 0 ∧ b > 0 ∧ a ^ 2 + b ^ 2 = 1 →
    1 < a + b ∧ a + b ≤ Real.sqrt 2 := by
  rintro a b ⟨ha, hb, he⟩
  constructor
  · nlinarith [mul_pos ha hb]
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (a - b)]

#print axioms solution
