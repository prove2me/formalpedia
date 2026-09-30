-- Prove2me | solution 1 for lean_workbook_plus_14094
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:09.294263+00:00
-- url     : https://prove2.me/submissions/98196778-d71d-4ab5-a66c-08986566140f

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ) (i : ℕ) (hi : x^2 ≤ i ∧ i < (x + 1)^2) : ⌊Real.sqrt i⌋ = x := by
  rw [Real.floor_real_sqrt_eq_nat_sqrt]
  norm_cast
  exact (Nat.eq_sqrt'.mpr hi).symm
