-- Prove2me | solution 1 for tangent_coordinate_kernel_symm
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T18:28:31.913+00:00
-- url     : https://prove2.me/submissions/7e47755d-130d-472d-980c-3bad8dfaee07

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_tangent_projection_self_adjoint

open MatrixCompletion
open scoped Classical BigOperators

namespace ProveTangentKernelSymm

theorem matrix_inner_coordinate
    {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  classical
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hb
      simp at hb
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro y _
    simp [hx]
  · intro ha
    simp at ha

theorem coordinate_matrix_inner
    {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    matrixInner (coordinateMatrix a b) X = X a b := by
  classical
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hb
      simp at hb
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro y _
    simp [hx]
  · intro ha
    simp at ha

end ProveTangentKernelSymm

open ProveTangentKernelSymm

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i a : Fin n₁) (j b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      tangentCoordinateKernel S a b i j := by
  rw [tangentCoordinateKernel, tangentCoordinateKernel]
  rw [tangent_projection_self_adjoint]
  rw [coordinate_matrix_inner, matrix_inner_coordinate]
