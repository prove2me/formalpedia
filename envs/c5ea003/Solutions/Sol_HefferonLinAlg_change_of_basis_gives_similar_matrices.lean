-- Prove2me | solution 1 for HefferonLinAlg.change_of_basis_gives_similar_matrices
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T15:45:23.931521+00:00
-- url     : https://prove2.me/submissions/3a7dd34f-b735-44b7-ab82-f7397a55b413

import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

theorem solution
    {K : Type*} [Field K] {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (B C : Module.Basis (Fin n) K V) (t : V →ₗ[K] V) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧
      LinearMap.toMatrix C C t = P⁻¹ * LinearMap.toMatrix B B t * P := by
  classical
  refine ⟨B.toMatrix C, ?_, ?_⟩
  · exact Matrix.isUnit_det_of_left_inverse
      (Module.Basis.toMatrix_mul_toMatrix_flip C B)
  · rw [Matrix.inv_eq_left_inv (Module.Basis.toMatrix_mul_toMatrix_flip C B)]
    exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix C B C B t).symm
