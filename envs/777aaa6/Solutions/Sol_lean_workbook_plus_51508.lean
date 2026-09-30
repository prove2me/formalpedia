-- Prove2me | solution 1 for lean_workbook_plus_51508
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:54:43.324577+00:00
-- url     : https://prove2.me/submissions/ccf7fe40-bfcd-482c-b248-375242a4b082

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = A) (hBA : B * A = B) : (A - B) ^ 2 = 0 := by
  have hA : A * A = A := by
    calc
      A * A = (A * B) * A := by rw [hAB]
      _ = A * B := by rw [mul_assoc, hBA]
      _ = A := hAB
  have hB : B * B = B := by
    calc
      B * B = (B * A) * B := by rw [hBA]
      _ = B * A := by rw [mul_assoc, hAB]
      _ = B := hBA
  rw [pow_two, sub_mul, mul_sub, mul_sub, hA, hB, hAB, hBA]
  simp
