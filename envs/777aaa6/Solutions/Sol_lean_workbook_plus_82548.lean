-- Prove2me | solution 1 for lean_workbook_plus_82548
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:04.283938+00:00
-- url     : https://prove2.me/submissions/b6db2f6e-1bc4-4a9f-8ffb-9f20188d6b55

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Semiconj.Defs

theorem solution (R : Type*) [Ring R] (A B : Matrix (Fin 2) (Fin 2) R)
    (h : A * B = -(B * A)) :
    A ^ 3 * B = -(B * A ^ 3) ∧ A * B ^ 3 = -(B ^ 3 * A) := by
  have hab : SemiconjBy A B (-B) := by simpa only [SemiconjBy, neg_mul] using h
  have hba : B * A = -(A * B) := by rw [h, neg_neg]
  have hba' : SemiconjBy B A (-A) := by simpa only [SemiconjBy, neg_mul] using hba
  have hleft : B * A^3 = -(A^3 * B) := by
    simpa [SemiconjBy, pow_succ, neg_mul, mul_neg] using hba'.pow_right 3
  constructor
  · rw [hleft, neg_neg]
  · simpa [SemiconjBy, pow_succ, neg_mul, mul_neg] using hab.pow_right 3
