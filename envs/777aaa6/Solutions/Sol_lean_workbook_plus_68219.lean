-- Prove2me | solution 1 for lean_workbook_plus_68219
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:16.517903+00:00
-- url     : https://prove2.me/submissions/2df8ad14-cb28-46d9-af85-2b11ab338972

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution {x y z : ℤ} (hx : x ≠ y) (hy : y ≠ z) (hz : z ≠ x) :
    5 * (x - y) * (y - z) * (z - x) ∣
      (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5 := by
  refine ⟨x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x, ?_⟩
  ring

#print axioms solution
