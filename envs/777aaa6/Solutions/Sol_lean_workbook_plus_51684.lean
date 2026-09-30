-- Prove2me | solution 1 for lean_workbook_plus_51684
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:54:42.653648+00:00
-- url     : https://prove2.me/submissions/3c5f7d08-4ca1-4755-964b-4c64c1edd627

import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

theorem solution (R : Type*) [Ring R] (A B : Matrix (Fin 2) (Fin 2) R)
    (h : A * B = -(B * A)) : A ^ 2 * B ^ 2 = B ^ 2 * A ^ 2 := by
  have h2 : A ^ 2 * B = B * A ^ 2 := by
    calc
      A ^ 2 * B = A * (A * B) := by rw [pow_two, mul_assoc]
      _ = A * -(B * A) := by rw [h]
      _ = -(A * B) * A := by rw [mul_neg, neg_mul, mul_assoc]
      _ = B * A ^ 2 := by rw [h, neg_neg, pow_two, mul_assoc]
  calc
    A ^ 2 * B ^ 2 = (A ^ 2 * B) * B := by rw [pow_two B, mul_assoc]
    _ = (B * A ^ 2) * B := congrArg (fun C => C * B) h2
    _ = B * (A ^ 2 * B) := mul_assoc _ _ _
    _ = B * (B * A ^ 2) := congrArg (fun C => B * C) h2
    _ = B ^ 2 * A ^ 2 := by rw [pow_two B, mul_assoc]
