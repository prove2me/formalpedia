-- Prove2me | solution 1 for lean_workbook_plus_13241
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:57:12.343665+00:00
-- url     : https://prove2.me/submissions/1075e183-1e7c-473c-8f9a-2187dff5e8e9

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Semiconj.Defs

set_option autoImplicit false

theorem solution (R : Type*) [Ring R] (A B : Matrix (Fin 2) (Fin 2) R)
    (h : A * B = -(B * A)) : A ^ 3 * B ^ 3 = -(B ^ 3 * A ^ 3) := by
  have h1 : SemiconjBy A B (-B) := by simpa only [SemiconjBy, neg_mul] using h
  have h2 : A * B ^ 3 = -(B ^ 3 * A) := by
    simpa [SemiconjBy, pow_succ, neg_mul, mul_neg] using h1.pow_right 3
  have h3 : SemiconjBy (B ^ 3) A (-A) := by
    change B ^ 3 * A = -A * B ^ 3
    rw [neg_mul, h2, neg_neg]
  have h4 : B ^ 3 * A ^ 3 = -(A ^ 3 * B ^ 3) := by
    simpa [SemiconjBy, pow_succ, neg_mul, mul_neg] using h3.pow_right 3
  rw [h4, neg_neg]
