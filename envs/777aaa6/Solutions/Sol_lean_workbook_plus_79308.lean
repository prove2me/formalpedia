-- Prove2me | solution 1 for lean_workbook_plus_79308
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:47:00.412037+00:00
-- url     : https://prove2.me/submissions/a551ff16-90cc-4b54-9725-d1b47e6c832b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

theorem solution (m : ℕ) (x : ℤ) :
    (x^2 ≡ 1 [ZMOD m]) ↔ ((x-1)*(x+1) ≡ 0 [ZMOD m]) := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have he : 0 - (x - 1) * (x + 1) = 1 - x ^ 2 := by ring
  rw [he]

#print axioms solution
