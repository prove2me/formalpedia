-- Prove2me | solution 1 for lean_workbook_plus_37502
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:04:09.722174+00:00
-- url     : https://prove2.me/submissions/71c05e2a-5cce-4292-b128-f5f07d2801a4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution (x y z : ℤ) (h₁ : y = 2 * z) :
    (x + 2) ^ 4 - x ^ 4 = y ^ 3 ↔
      x ^ 3 + 3 * x ^ 2 + 4 * x + 2 = z ^ 3 := by
  rw [h₁]
  have he : (x + 2) ^ 4 - x ^ 4 = 8 * (x ^ 3 + 3 * x ^ 2 + 4 * x + 2) := by
    ring
  rw [he]
  constructor <;> intro h <;> nlinarith

#print axioms solution
