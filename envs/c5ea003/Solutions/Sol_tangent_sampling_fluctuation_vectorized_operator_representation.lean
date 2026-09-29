-- Prove2me | solution 1 for tangent_sampling_fluctuation_vectorized_operator_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T17:04:02.537606+00:00
-- url     : https://prove2.me/submissions/114d0617-f04d-4662-9f97-e890a9ab42c0

import Theorems.Thm_tangent_sampling_fluctuation_rank_one_frame_identity
import Theorems.Thm_tangent_projection_self_adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic

open MatrixCompletion
open scoped BigOperators Matrix Classical

/-- Source: Candès-Recht arXiv:0805.4471, §4.2, equations (4.6)--(4.9);
Rudelson, J. Funct. Anal. 164 (1999), Theorem 1 proof pp. 3--6; van Handel,
"Structured Random Matrices", §3.

The proof combines the rank-one frame representation of
`P_T(P_Ω X)-pX` with Frobenius self-adjointness of `P_T`. -/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    (fun e : Fin n1 × Fin n2 =>
        (tangentProjection S (samplingProjection Omega X) - p • X) e.1 e.2)
      = (∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1 : Real) else 0) - p) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))).mulVec
          (fun e : Fin n1 × Fin n2 => X e.1 e.2) := by
  classical
  set y : Fin n1 × Fin n2 → RealMatrix n1 n2 :=
    fun ab => tangentProjection S (coordinateMatrix ab.1 ab.2) with hy
  have hC : ∀ ab : Fin n1 × Fin n2, ∀ e : Fin n1 × Fin n2,
      (Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)
          (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)).mulVec
        (fun e : Fin n1 × Fin n2 => X e.1 e.2) e
        = (matrixInner (y ab) X) * (y ab e.1 e.2) := by
    intro ab e
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, matrixInner]
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hval : ∀ ab : Fin n1 × Fin n2, matrixInner (y ab) X = X ab.1 ab.2 := by
    intro ab
    have h1 : matrixInner (y ab) X
        = matrixInner (coordinateMatrix ab.1 ab.2) (tangentProjection S X) := by
      rw [hy]; simp only
      exact tangent_projection_self_adjoint S (coordinateMatrix ab.1 ab.2) X
    rw [h1, hX]
    simp only [matrixInner, coordinateMatrix]
    rw [Finset.sum_eq_single ab.1]
    · rw [Finset.sum_eq_single ab.2]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ ab.2) h
    · intro a _ ha
      apply Finset.sum_eq_zero; intro b _; simp [ha]
    · intro h; exact absurd (Finset.mem_univ ab.1) h
  have hRHS : ∀ e : Fin n1 × Fin n2,
      ((∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1 : Real) else 0) - p) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)
              (fun e : Fin n1 × Fin n2 => y ab e.1 e.2))).mulVec
          (fun e : Fin n1 × Fin n2 => X e.1 e.2)) e
        = ∑ ab : Fin n1 × Fin n2,
            ((if ab ∈ Omega then (1 : Real) else 0) - p)
              * ((Matrix.vecMulVec
                    (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)
                    (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)).mulVec
                  (fun e : Fin n1 × Fin n2 => X e.1 e.2) e) := by
    intro e
    have hrow : (∑ ab : Fin n1 × Fin n2,
        (((if ab ∈ Omega then (1 : Real) else 0) - p) •
          Matrix.vecMulVec
            (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)
            (fun e : Fin n1 × Fin n2 => y ab e.1 e.2))) e
        = ∑ ab : Fin n1 × Fin n2,
            (((if ab ∈ Omega then (1 : Real) else 0) - p) •
              Matrix.vecMulVec
                (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)
                (fun e : Fin n1 × Fin n2 => y ab e.1 e.2)) e := Finset.sum_apply e _ _
    simp only [Matrix.mulVec, dotProduct]
    conv_lhs => rw [hrow]
    simp only [Finset.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ab _
    apply Finset.sum_congr rfl; intro x _
    ring
  funext e
  rw [hRHS e]
  rw [tangent_sampling_fluctuation_rank_one_frame_identity S Omega p X hX]
  rw [Matrix.sum_apply e.1 e.2]
  simp only [Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro ab _
  rw [hC ab e, hval ab]
  simp only [hy]
  ring
