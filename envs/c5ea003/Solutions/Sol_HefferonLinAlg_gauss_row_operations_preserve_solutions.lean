-- Prove2me | solution 1 for HefferonLinAlg.gauss_row_operations_preserve_solutions
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:45:18.234562+00:00
-- url     : https://prove2.me/submissions/80eb900a-0b63-41fd-9f44-ae76d6798132

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

theorem solution
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K)
    (M : Matrix (Fin m) (Fin m) K) (hM : IsUnit M.det) (x : Fin n → K) :
    A *ᵥ x = b ↔ (M * A) *ᵥ x = M *ᵥ b := by
  rw [← Matrix.mulVec_mulVec]
  constructor
  · exact congrArg M.mulVec
  · intro h
    exact Matrix.mulVec_injective_of_isUnit (M.isUnit_iff_isUnit_det.mpr hM) h
