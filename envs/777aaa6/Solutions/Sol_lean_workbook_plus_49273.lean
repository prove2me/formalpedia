-- Prove2me | solution 1 for lean_workbook_plus_49273
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:49:01.017297+00:00
-- url     : https://prove2.me/submissions/9dd4946d-6b10-4c13-8370-280811e598fd

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LinearCombination

theorem solution (x y z : ℤ)
    (h : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = x * y * z) :
    (x + y + z + 6) ∣ (x ^ 3 + y ^ 3 + z ^ 3) := by
  refine ⟨x ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z, ?_⟩
  linear_combination -3 * h

#print axioms solution
