-- Prove2me | Theorems.Thm_tangent_sampling_deviation_le_vectorized_operator_norm
-- name    : tangent_sampling_deviation_le_vectorized_operator_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T17:05:25.929692+00:00
-- url     : https://prove2.me/theorems/40783392-c8bf-4ed2-8448-d6fdabefa023
-- statement:
--   **Operator-norm upper bound for the tangent sampling deviation.**
--
--   For fixed sampled entries $\Omega$ and sampling rate $p$, define
--   $$
--   A_\Omega=\sum_{a,b}(\delta_{ab}-p)\,\operatorname{vec}(P_T(e_ae_b^*))\operatorname{vec}(P_T(e_ae_b^*))^\top.
--   $$
--   Then the Candes--Recht tangent sampling deviation
--   $$
--   Z(\Omega)=p^{-1}\sup_{X\in T,\ \|X\|_F\le1}\|P_T(P_\Omega X)-pX\|_F
--   $$
--   is bounded by
--   $$
--   Z(\Omega)\le p^{-1}\|A_\Omega\|_{\ell_2\to\ell_2}.
--   $$
--   This is the easy direction needed for Rudelson's selection argument: after vectorization, each admissible $X$ has Euclidean norm at most $1$, so the supremum is bounded by the operator norm of $A_\Omega$.
--
--   Reference location: Candes--Recht, arXiv:0805.4471, Section 4.2, equations (4.6)--(4.9), and the Rudelson selection theorem setup following equation (4.9).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

open MatrixCompletion
open scoped BigOperators Matrix Classical Matrix.Norms.L2Operator

/-- The tangent sampling deviation is bounded by the L2 operator norm of the
vectorized rank-one Bernoulli fluctuation matrix. This is the easy `sSup ≤
operator norm` direction needed in the Rudelson self-bounding assembly. -/

theorem tangent_sampling_deviation_le_vectorized_operator_norm
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 ≤ p⁻¹) :
    tangentSamplingDeviation Omega S p
      ≤ p⁻¹ * ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
          (∑ ab : Fin n1 × Fin n2,
            (((if ab ∈ Omega then (1 : Real) else 0) - p) •
              Matrix.vecMulVec
                (fun e : Fin n1 × Fin n2 =>
                  tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                (fun e : Fin n1 × Fin n2 =>
                  tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖ := by
  sorry
