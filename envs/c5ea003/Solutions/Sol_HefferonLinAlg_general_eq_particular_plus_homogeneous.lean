-- Prove2me | solution 1 for HefferonLinAlg.general_eq_particular_plus_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T16:45:18.599995+00:00
-- url     : https://prove2.me/submissions/26cbecd6-33f3-4177-b6cb-6ad6ed7352ad

import Mathlib.Data.Matrix.Mul

open Matrix

theorem solution
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (p : Fin n → K) (hp : A *ᵥ p = b) :
    {x : Fin n → K | A *ᵥ x = b} = {x : Fin n → K | ∃ h, A *ᵥ h = 0 ∧ x = p + h} := by
  ext x
  constructor
  · intro hx
    refine ⟨x - p, ?_, ?_⟩
    · rw [Matrix.mulVec_sub, hx, hp, sub_self]
    · simp
  · rintro ⟨h, hh, rfl⟩
    change A *ᵥ (p + h) = b
    rw [Matrix.mulVec_add, hp, hh, add_zero]
