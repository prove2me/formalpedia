-- Prove2me | solution 1 for hs_vectorization_isometry_intertwines_rank_one_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-24T01:39:37.01086+00:00
-- url     : https://prove2.me/submissions/37862273-41d0-4fda-ab8d-20f0d4beb655

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) :
    (∀ X Y : RealMatrix n1 n2,
        matrixInner X Y
          = (fun e : Fin n1 × Fin n2 => X e.1 e.2)
              ⬝ᵥ (fun e : Fin n1 × Fin n2 => Y e.1 e.2)) ∧
    (∀ X : RealMatrix n1 n2,
        frobeniusNormSq X
          = (fun e : Fin n1 × Fin n2 => X e.1 e.2)
              ⬝ᵥ (fun e : Fin n1 × Fin n2 => X e.1 e.2)) ∧
    (∀ (a : Fin n1) (b : Fin n2) (H : RealMatrix n1 n2),
        (Matrix.vecMulVec
            (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix a b) e.1 e.2)
            (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix a b) e.1 e.2)).mulVec
          (fun e : Fin n1 × Fin n2 => H e.1 e.2)
          = (matrixInner (tangentProjection S (coordinateMatrix a b)) H)
              • (fun e : Fin n1 × Fin n2 => tangentProjection S (coordinateMatrix a b) e.1 e.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    unfold matrixInner dotProduct
    rw [Fintype.sum_prod_type]
  · intro X
    unfold frobeniusNormSq dotProduct
    simp only [← pow_two]
    rw [Fintype.sum_prod_type]
  · intro a b H
    funext e
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, matrixInner,
      Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    ring
